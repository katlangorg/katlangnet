using System.Text;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// Shared optimized-versus-generic STRUCTURED diagnostic parity machinery for the
/// loop planner.
///
/// <para>The loop optimizer is a C#-only execution strategy over the generic Lean
/// loop semantics (see <c>src/KatLang/SEMANTIC-ALIGNMENT.md</c>, row "Optimized
/// loops": no Lean update, equivalence tests required), so its contract is pinned
/// as exact optimized-vs-generic diagnostic equivalence — error kind, complete
/// context chain, span, and the WHOLE structured error tree node by node — never
/// by relaxing either side. Used by
/// <see cref="LoopPlannedIfDiagnosticParityTests"/> and
/// <see cref="LoopPlannedUnaryDiagnosticParityTests"/>.</para>
/// </summary>
internal static class LoopDiagnosticParityAssertions
{
    internal static Expr Program(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    internal static EvalResult<Result> Run(string source, bool enableLoopOptimization)
        => Evaluator.Run(
            Program(source),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization);

    internal static (
        EvalResult<Result> Result,
        LoopOptimizationDiagnosticsSnapshot Loop,
        ZeroArgPropertyResultCacheSnapshot Cache) RunObserved(string source, bool enableLoopOptimization)
    {
        var cache = new RunScopedZeroArgPropertyResultCache();
        var loopDiagnostics = new LoopOptimizationDiagnostics();
        var result = Evaluator.Run(Program(source), cache, enableLoopOptimization, loopDiagnostics);
        return (result, loopDiagnostics.GetSnapshot(), cache.GetSnapshot());
    }

    internal static (
        EvalResult<Evaluator.CountedResult> Result,
        LoopOptimizationDiagnosticsSnapshot Loop) RunCountedObserved(
            string source,
            bool enableLoopOptimization)
    {
        var loopDiagnostics = new LoopOptimizationDiagnostics();
        var result = Evaluator.RunCountedObserved(
            Program(source),
            enableOptimizations: enableLoopOptimization,
            zeroArgPropertyResultCache: new RunScopedZeroArgPropertyResultCache(),
            loopDiagnostics: loopDiagnostics).Result;
        return (result, loopDiagnostics.GetSnapshot());
    }

    internal static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }

    /// <summary>Ordered outermost-to-innermost legacy context spellings.</summary>
    internal static IReadOnlyList<string> ContextChain(EvalError error)
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
    internal static string CacheCounters(ZeroArgPropertyResultCacheSnapshot snapshot)
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

    internal static (int? StartLine, int? StartColumn, int? EndLine, int? EndColumn) Span(EvalError error)
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

    internal static string DescribeErrorTree(EvalError error)
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
            TextErrorContext(var message) => $"Text[{Text(message)}]",
            PropertyEvaluationContext(var propertyName) => $"Property[{Text(propertyName)}]",
            ProgramEvaluationContext => "Program[]",
            DotCallContext(var receiver, var propertyName) => $"DotCall[{Text(receiver)}|{Text(propertyName)}]",
            CallContext(var callee) => $"Call[{Text(callee)}]",
            ReduceInitialAccumulatorContext(var requiredNames) =>
                $"ReduceInitialAccumulator[{TextList(requiredNames)}]",
            LoopStateBindingContext(var loopName, var stepParams, var actualCount) =>
                $"LoopStateBinding[{Text(loopName)}|{TextList(stepParams)}|{actualCount}]",
            VariadicLoopStateBindingContext(var loopName, var stepParams, var expectedMin, var actualCount) =>
                $"VariadicLoopStateBinding[{Text(loopName)}|{TextList(stepParams)}|{expectedMin}|{actualCount}]",
            DeconstructionBindingContext(var targets, var hasCollecting) =>
                $"DeconstructionBinding[{TextList(targets)}|{hasCollecting}]",
            SequenceValueParameterBindingContext(var patternDisplayName, var hasCollectingItem) =>
                $"SequenceValueParameterBinding[{Text(patternDisplayName)}|{hasCollectingItem}]",
            OpenResolutionContext(var openDescription) => $"Open[{Text(openDescription)}]",
            ImplicitParameterContext(var paramNames, var providedCount) =>
                $"ImplicitParameter[{TextList(paramNames)}|{providedCount}]",
            _ => throw new Xunit.Sdk.XunitException(
                $"DescribeContext does not handle context kind '{context.GetType().Name}'; extend it so structured comparisons stay faithful."),
        };

    private static string DescribeLeafPayload(EvalError error)
        => error switch
        {
            EvalError.UnknownName(var name) => $"[{Text(name)}]",
            EvalError.UnknownProperty(var objectDesc, var propertyName) => $"[{Text(objectDesc)}|{Text(propertyName)}]",
            EvalError.NotPublicProperty(var objectDesc, var propertyName) => $"[{Text(objectDesc)}|{Text(propertyName)}]",
            EvalError.LocalOnlyProperty(var objectDesc, var propertyName, var exposure) => $"[{Text(objectDesc)}|{Text(propertyName)}|{exposure}]",
            EvalError.NotAnAlgorithm(var description) => $"[{Text(description)}]",
            EvalError.IllegalInOpen(var reason) => $"[{Text(reason)}]",
            EvalError.BadOpenForm(var reason) => $"[{Text(reason)}]",
            EvalError.IllegalInEval(var reason) => $"[{Text(reason)}]",
            EvalError.AmbiguousOpen(var name, var providers) => $"[{Text(name)}|{TextList(providers)}]",
            EvalError.ArityMismatch(var expected, var actual) { Signature: var signature } arity =>
                $"[{expected}|{actual}|{DescribeSignature(signature)}|{DescribeProvenances(arity.InferredImplicitParameters)}]",
            EvalError.VariadicArityMismatch(var calleeName, var expectedMinimum, var actual) { Signature: var signature } =>
                $"[{Text(calleeName)}|{expectedMinimum}|{actual}|{DescribeSignature(signature)}]",
            EvalError.TypeMismatch(var message) => $"[{Text(message)}]",
            EvalError.NoMatchingBranch(var algorithmName) => $"[{Text(algorithmName)}]",
            EvalError.BranchArityMismatch(var algorithmName, var expected, var actual) => $"[{Text(algorithmName)}|{expected}|{actual}]",
            EvalError.BranchOutputArityMismatch(var algorithmName, var expected, var actual) => $"[{Text(algorithmName)}|{expected}|{actual}]",
            EvalError.DuplicateProperty(var name) => $"[{Text(name)}]",
            EvalError.UnresolvedImplicitParams(var paramNames) unresolved =>
                $"[{TextList(paramNames)}|{DescribeProvenances(unresolved.InferredImplicitParameters)}]",
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
    /// Length-prefix strings and count-prefix lists so distinct structured payloads
    /// cannot collapse to the same comparison text (for example, one provider named
    /// <c>a,b</c> versus two providers named <c>a</c> and <c>b</c>).
    /// </summary>
    private static string Text(string? value)
        => value is null ? "null" : $"{value.Length}:{value}";

    private static string TextList(IReadOnlyList<string> values)
        => $"{values.Count}[{string.Concat(values.Select(Text))}]";

    private static string DescribeSignature(CallableSignature? signature)
    {
        if (signature is null)
            return "null";

        return $"Signature[name={Text(signature.Name)}"
            + $"|patterns={DescribePatterns(signature.ParameterPatterns)}"
            + $"|parameters={signature.Parameters.Count}[{string.Concat(signature.Parameters.Select(DescribeParameter))}]"
            + $"|parameterNames={TextList(signature.ParameterNames)}"
            + $"|explicit={signature.HasExplicitParameterList}"
            + $"|display={Text(signature.DisplayText)}]";
    }

    private static string DescribeParameter(CallableParameter parameter)
        => $"Parameter[name={Text(parameter.Name)}|kind={parameter.Kind}|source={parameter.Source}"
            + $"|pattern={DescribePattern(parameter.DeclaringPattern)}]";

    private static string DescribePatterns(IReadOnlyList<ParameterPattern> patterns)
        => $"{patterns.Count}[{string.Concat(patterns.Select(DescribePattern))}]";

    private static string DescribePattern(ParameterPattern? pattern)
        => pattern switch
        {
            null => "null",
            CaptureParameterPattern capture =>
                $"Capture[name={Text(capture.Name)}|span={SpanText(capture.Span)}|kind={capture.Kind}"
                + $"|collectSpan={SpanText(capture.CollectMarkerSpan)}"
                + $"|provenance={DescribeProvenance(capture.InferredProvenance)}]",
            SequenceValueParameterPattern sequence => $"Sequence[{DescribePatterns(sequence.Items)}]",
            _ => throw new Xunit.Sdk.XunitException(
                $"DescribePattern does not handle pattern kind '{pattern.GetType().Name}'; extend it so structured comparisons stay faithful."),
        };

    private static string DescribeProvenances(IReadOnlyList<ImplicitParameterProvenance>? provenances)
        => provenances is null
            ? "null"
            : $"{provenances.Count}[{string.Concat(provenances.Select(DescribeProvenance))}]";

    private static string DescribeProvenance(ImplicitParameterProvenance? provenance)
        => provenance is null
            ? "null"
            : $"Provenance[name={Text(provenance.Name)}|span={SpanText(provenance.Span)}"
                + $"|suggestion={Text(provenance.SuggestedName)}]";

    /// <summary>
    /// The complete observable diagnostic of an optimization-eligible failing
    /// program must be identical with the optimizer on and off: the ENTIRE
    /// structured error tree node by node (types, per-node spans, context
    /// payloads, type-specific payloads), plus the rendered message and span.
    /// </summary>
    internal static EvalError AssertOptimizerTransparentFailure(string source)
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
}

public class LoopDiagnosticParityAssertionsTests
{
    [Fact]
    public void StructuredDescription_DistinguishesListPayloadBoundaries()
    {
        var oneProvider = new EvalError.AmbiguousOpen("X", ["A,B"]);
        var twoProviders = new EvalError.AmbiguousOpen("X", ["A", "B"]);

        Assert.NotEqual(
            LoopDiagnosticParityAssertions.DescribeErrorTree(oneProvider),
            LoopDiagnosticParityAssertions.DescribeErrorTree(twoProviders));
    }

    [Fact]
    public void StructuredDescription_IncludesSignatureStructureBeyondDisplayText()
    {
        var explicitSignature = new CallableSignature(
            "F",
            [new CallableParameter("x", Source: CallableParameterSource.Explicit)]);
        var implicitSignature = new CallableSignature(
            "F",
            [new CallableParameter("x", Source: CallableParameterSource.Implicit)]);
        Assert.Equal(explicitSignature.DisplayText, implicitSignature.DisplayText);

        var explicitError = new EvalError.ArityMismatch(1, 0) { Signature = explicitSignature };
        var implicitError = new EvalError.ArityMismatch(1, 0) { Signature = implicitSignature };

        Assert.NotEqual(
            LoopDiagnosticParityAssertions.DescribeErrorTree(explicitError),
            LoopDiagnosticParityAssertions.DescribeErrorTree(implicitError));
    }

    [Fact]
    public void StructuredDescription_IncludesDiagnosticProvenance()
    {
        var withoutProvenance = new EvalError.UnresolvedImplicitParams(["missing"]);
        var withProvenance = new EvalError.UnresolvedImplicitParams(["missing"])
        {
            InferredImplicitParameters =
            [
                new ImplicitParameterProvenance(
                    "missing",
                    new SourceSpan(4, 7, 4, 13),
                    suggestion: null),
            ],
        };

        Assert.NotEqual(
            LoopDiagnosticParityAssertions.DescribeErrorTree(withoutProvenance),
            LoopDiagnosticParityAssertions.DescribeErrorTree(withProvenance));
    }
}
