using KatLang.Evaluation;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

/// <summary>
/// Structural regressions for the sequence-pipeline DISPATCH ordering (M15):
/// recognition runs before the evaluation-services bundle is constructed, so the
/// bundle — whose captured delegates are the probe's only allocations — exists only
/// for syntactically recognized candidates on fusion-enabled runs.
///
/// <para>The oracle is the passive run-scoped
/// <see cref="EvaluationObservations.SequencePipelineServiceConstructionCount"/>
/// counter recorded at the single construction site in
/// <c>Evaluator.TryEvaluateSequencePipeline</c> — never CLR allocation totals, so
/// the pins are deterministic under JIT/runtime noise. Alongside it, the
/// diagnostics-channel pins keep the pre-existing instrumentation contract exact:
/// a fusion-disabled run with diagnostics attached still records the
/// "sequence pipeline optimization disabled" fallback for recognized shapes, and a
/// syntactic near-miss still records its shape reason, both without services.</para>
/// </summary>
public class SequencePipelineDispatchTests
{
    private static Expr Program(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private const int NonCandidateRowCount = 250;

    /// <summary>
    /// 250 output rows, each evaluating two plain non-candidate calls (500 call
    /// dispatches through the sequence-pipeline probe), plus one builtin call row.
    /// </summary>
    private static string NonCandidateCallSource()
    {
        var rows = string.Join(
            "\n",
            Enumerable.Range(1, NonCandidateRowCount).Select(i => $"Add({i}, 1) + Add({i}, 2)"));
        return $"Add(a, b) = a + b\n{rows}\nsum((1, 2, 3))";
    }

    /// <summary>
    /// 250 output rows, each evaluating two non-candidate dot-calls (500 dot-call
    /// dispatches through the probe), plus two bare <c>.count</c> rows — the most
    /// candidate-like miss (the count name matches but the receiver is not a
    /// <c>.filter</c> dot edge).
    /// </summary>
    private static string NonCandidateDotCallSource()
    {
        var rows = string.Join(
            "\n",
            Enumerable.Range(1, NonCandidateRowCount).Select(i => $"V.Add({i}) + V.Add({i} + 1)"));
        return $"Add(a, b) = a + b\nV = 10\n{rows}\n(1, 2, 3).count\nV.count";
    }

    [Fact]
    public void NonCandidateCalls_ConstructNoPipelineServices()
    {
        var observations = new EvaluationObservations();
        var result = Evaluator.RunObserved(Program(NonCandidateCallSource()), observations);

        Assert.False(result.IsError, $"non-candidate call program failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal(NonCandidateRowCount + 1, result.Value.ToAtoms().Count);
        Assert.Equal(0, observations.SequencePipelineServiceConstructionCount);
    }

    [Fact]
    public void NonCandidateDotCalls_ConstructNoPipelineServices()
    {
        var observations = new EvaluationObservations();
        var result = Evaluator.RunObserved(Program(NonCandidateDotCallSource()), observations);

        Assert.False(result.IsError, $"non-candidate dot-call program failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal(NonCandidateRowCount + 2, result.Value.ToAtoms().Count);
        Assert.Equal(0, observations.SequencePipelineServiceConstructionCount);
    }

    public static TheoryData<string, string, decimal> RecognizedCandidates() => new()
    {
        { "dot-filter-dot-count / direct range", "IsEven = x mod 2 == 0\nrange(1, 10).filter(IsEven).count", 5m },
        { "plain-count-dot-filter / direct range", "IsEven = x mod 2 == 0\ncount(range(1, 10).filter(IsEven))", 5m },
        { "plain-count-plain-filter / direct range", "IsEven = x mod 2 == 0\ncount(filter(range(1, 10), IsEven))", 5m },
        { "dot-filter-dot-count / generic source", "IsEven = x mod 2 == 0\nData = 1, 2, 3, 4\nData.filter(IsEven).count", 2m },
    };

    [Theory]
    [MemberData(nameof(RecognizedCandidates))]
    public void RecognizedCandidate_ConstructsServicesExactlyOnce_AndFuses(string form, string source, decimal expected)
    {
        Assert.False(string.IsNullOrEmpty(form));

        var observations = new EvaluationObservations();
        var diagnostics = new SequencePipelineDiagnostics();
        var (result, _) = Evaluator.RunCountedObserved(
            Program(source),
            sequenceDiagnostics: diagnostics,
            observations: observations);

        Assert.False(result.IsError, $"candidate program failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal([expected], result.Value.Value.ToAtoms());
        Assert.Equal(1, observations.SequencePipelineServiceConstructionCount);
        Assert.Equal(1, diagnostics.GetSnapshot().FilterCountFusionHits);
    }

    [Theory]
    [MemberData(nameof(RecognizedCandidates))]
    public void FusionDisabled_ConstructsNoPipelineServices_AndResultUnchanged(string form, string source, decimal expected)
    {
        Assert.False(string.IsNullOrEmpty(form));

        // Disabled run with NO diagnostics attached — the production shape of a
        // fusion-disabled run. It must skip pipeline work entirely (no services)
        // and produce the ordinary generic result.
        var observations = new EvaluationObservations();
        var result = Evaluator.RunObserved(Program(source), observations, enableOptimizations: false);

        Assert.False(result.IsError, $"disabled-mode program failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal([expected], result.Value.ToAtoms());
        Assert.Equal(0, observations.SequencePipelineServiceConstructionCount);
    }

    [Fact]
    public void FusionDisabledWithDiagnostics_RecordsDisabledFallback_WithoutServices()
    {
        // The pre-existing instrumentation contract: with the internal diagnostics
        // collector attached, a fusion-disabled run still RECOGNIZES candidate
        // shapes and records the disabled fallback — but recognition alone must not
        // construct evaluation services.
        var source = "IsEven = x mod 2 == 0\nrange(1, 10).filter(IsEven).count";
        var observations = new EvaluationObservations();
        var diagnostics = new SequencePipelineDiagnostics();
        var (result, _) = Evaluator.RunCountedObserved(
            Program(source),
            enableOptimizations: false,
            sequenceDiagnostics: diagnostics,
            observations: observations);

        Assert.False(result.IsError);
        Assert.Equal([5m], result.Value.Value.ToAtoms());
        Assert.Equal(0, observations.SequencePipelineServiceConstructionCount);

        var stats = diagnostics.GetSnapshot();
        Assert.Equal(0, stats.FilterCountFusionHits);
        Assert.Equal(1, stats.FilterCountFusionFallbacks);
        Assert.Equal(1, stats.FallbackReasons["sequence pipeline optimization disabled"]);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void UnrelatedCallsWithDiagnostics_RecordNothing_AndConstructNoServices(bool enableOptimizations)
    {
        // Diagnostics reachability must not turn a wholly unrelated plain call or
        // dot-call into a near miss. In disabled mode this also proves that the
        // preserved diagnostic recognizer does not invent the generic "disabled"
        // reason for syntax it never recognized.
        var source = "Add(a, b) = a + b\nAdd(1, 2)\n3.Add(4)";
        var observations = new EvaluationObservations();
        var diagnostics = new SequencePipelineDiagnostics();
        var (result, _) = Evaluator.RunCountedObserved(
            Program(source),
            enableOptimizations: enableOptimizations,
            sequenceDiagnostics: diagnostics,
            observations: observations);

        Assert.False(result.IsError, $"unrelated-call program failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal([3m, 7m], result.Value.Value.ToAtoms());
        Assert.Equal(0, observations.SequencePipelineServiceConstructionCount);

        var stats = diagnostics.GetSnapshot();
        Assert.Equal(0, stats.FilterCountFusionHits);
        Assert.Equal(0, stats.FilterCountFusionFallbacks);
        Assert.Empty(stats.FallbackReasons);
        Assert.Empty(stats.Pipelines);
    }

    [Fact]
    public void SyntacticNearMiss_RecordsShapeFallback_WithoutServices()
    {
        // `count(candidate, extra)` is a recognition MISS with a recorded reason:
        // the near-miss diagnostic survives the reorder, and no services exist for
        // it. (The two-argument count itself is an ordinary arity error.)
        var source = "IsEven = x mod 2 == 0\ncount(range(1, 4).filter(IsEven), 1)";
        var observations = new EvaluationObservations();
        var diagnostics = new SequencePipelineDiagnostics();
        var (result, _) = Evaluator.RunCountedObserved(
            Program(source),
            sequenceDiagnostics: diagnostics,
            observations: observations);

        Assert.True(result.IsError, "two-argument count must remain an ordinary arity error");
        Assert.Equal(0, observations.SequencePipelineServiceConstructionCount);

        var stats = diagnostics.GetSnapshot();
        Assert.Equal(0, stats.FilterCountFusionHits);
        Assert.Equal(1, stats.FallbackReasons["unsupported count argument shape"]);
    }

    [Fact]
    public void FusionDisabledSyntacticNearMiss_PreservesShapeReason_WithoutServices()
    {
        // Recognition preceded the disabled gate before M15. With diagnostics
        // attached, an unsupported candidate shape must therefore retain its
        // specific syntax reason instead of being reclassified as merely disabled.
        var source = "IsEven = x mod 2 == 0\ncount(range(1, 4).filter(IsEven), 1)";
        var observations = new EvaluationObservations();
        var diagnostics = new SequencePipelineDiagnostics();
        var (result, _) = Evaluator.RunCountedObserved(
            Program(source),
            enableOptimizations: false,
            sequenceDiagnostics: diagnostics,
            observations: observations);

        Assert.True(result.IsError, "two-argument count must remain an ordinary arity error");
        Assert.Equal(0, observations.SequencePipelineServiceConstructionCount);

        var stats = diagnostics.GetSnapshot();
        Assert.Equal(1, stats.FilterCountFusionFallbacks);
        Assert.Equal(1, stats.FallbackReasons["unsupported count argument shape"]);
        Assert.DoesNotContain("sequence pipeline optimization disabled", stats.FallbackReasons.Keys);
    }

    public static TheoryData<string, string, decimal> ShadowedCountCandidates() => new()
    {
        {
            "dot / root-local",
            "count(collection) = 123\nIsEven = x mod 2 == 0\nrange(1, 10).filter(IsEven).count",
            123m
        },
        {
            "plain / root-local",
            "count(collection) = 234\nIsEven = x mod 2 == 0\ncount(range(1, 10).filter(IsEven))",
            234m
        },
        {
            "dot / nested-local",
            "Use = { count(collection) = 345\nIsEven = x mod 2 == 0\nrange(1, 10).filter(IsEven).count }\nUse",
            345m
        },
    };

    [Theory]
    [MemberData(nameof(ShadowedCountCandidates))]
    public void ShadowedCountBuiltin_ConstructsServicesButRunsTheUserAlgorithm(
        string form,
        string source,
        decimal expected)
    {
        // A user-shadowed `count` is a SYNTACTIC candidate, so the probe constructs
        // services once to consult resolution — and resolution (never spelling)
        // decides: the lookup stage reports the shadow, fusion falls back, and the
        // user algorithm executes. This pins both the resolution-precedence rule
        // and the documented residual service construction for shape-recognized
        // near-candidates.
        Assert.False(string.IsNullOrEmpty(form));

        var observations = new EvaluationObservations();
        var diagnostics = new SequencePipelineDiagnostics();
        var (result, _) = Evaluator.RunCountedObserved(
            Program(source),
            sequenceDiagnostics: diagnostics,
            observations: observations);
        var genericResult = Evaluator.RunObserved(
            Program(source),
            new EvaluationObservations(),
            enableOptimizations: false);

        Assert.False(result.IsError, $"shadowed-count program failed: {(result.IsError ? result.Error : null)}");
        Assert.False(genericResult.IsError, $"generic shadowed-count program failed: {(genericResult.IsError ? genericResult.Error : null)}");
        Assert.Equal(genericResult.Value.ToAtoms(), result.Value.Value.ToAtoms());
        Assert.Equal([expected], result.Value.Value.ToAtoms());
        Assert.Equal(1, observations.SequencePipelineServiceConstructionCount);

        var stats = diagnostics.GetSnapshot();
        Assert.Equal(0, stats.FilterCountFusionHits);
        Assert.Equal(1, stats.FallbackReasons["count does not resolve to builtin"]);
    }

    public static TheoryData<string, string, string> ShadowedFilterCandidates() => new()
    {
        {
            "dot / root-local",
            "filter(*source, predicate) = 123\nIsEven = x mod 2 == 0\nrange(1, 10).filter(IsEven).count",
            "filter does not resolve to builtin"
        },
        {
            "plain / root-local",
            "filter(*source, predicate) = 123\nIsEven = x mod 2 == 0\ncount(filter(range(1, 10), IsEven))",
            "filter does not resolve to builtin"
        },
        {
            "dot / nested-local",
            "Use = { filter(*source, predicate) = 123\nIsEven = x mod 2 == 0\nrange(1, 10).filter(IsEven).count }\nUse",
            "filter does not resolve to builtin"
        },
        {
            "dot / structural member",
            "Source = { public filter(predicate) = 42 }\nIsEven = x mod 2 == 0\nSource.filter(IsEven).count",
            "filter is shadowed by a structural property"
        },
    };

    [Theory]
    [MemberData(nameof(ShadowedFilterCandidates))]
    public void ShadowedFilterBuiltin_ConstructsServicesButPreservesGenericResolution(
        string form,
        string source,
        string fallbackReason)
    {
        Assert.False(string.IsNullOrEmpty(form));

        var observations = new EvaluationObservations();
        var diagnostics = new SequencePipelineDiagnostics();
        var (result, _) = Evaluator.RunCountedObserved(
            Program(source),
            sequenceDiagnostics: diagnostics,
            observations: observations);
        var genericResult = Evaluator.RunObserved(
            Program(source),
            new EvaluationObservations(),
            enableOptimizations: false);

        Assert.False(result.IsError, $"shadowed-filter program failed: {(result.IsError ? result.Error : null)}");
        Assert.False(genericResult.IsError, $"generic shadowed-filter program failed: {(genericResult.IsError ? genericResult.Error : null)}");
        Assert.Equal(genericResult.Value.ToAtoms(), result.Value.Value.ToAtoms());
        Assert.Equal([1m], result.Value.Value.ToAtoms());
        Assert.Equal(1, observations.SequencePipelineServiceConstructionCount);

        var stats = diagnostics.GetSnapshot();
        Assert.Equal(0, stats.FilterCountFusionHits);
        Assert.Equal(1, stats.FilterCountFusionFallbacks);
        Assert.Equal(1, stats.FallbackReasons[fallbackReason]);
    }

    [Fact]
    public void CommittedSourceError_ConstructsServicesOnce_WithoutRecordingFallback()
    {
        // Range-bound evaluation starts only after the optimizer's depth commit.
        // The error is therefore handled by the optimized path, never handed back
        // for generic re-evaluation, but it occurs before a fusion hit is recorded.
        var source = "P(x) = 1\nrange(1 / 0, 3).filter(P).count";
        var observations = new EvaluationObservations();
        var diagnostics = new SequencePipelineDiagnostics();
        var (result, _) = Evaluator.RunCountedObserved(
            Program(source),
            sequenceDiagnostics: diagnostics,
            observations: observations);

        Assert.True(result.IsError);
        Assert.Equal(1, observations.SequencePipelineServiceConstructionCount);

        var stats = diagnostics.GetSnapshot();
        Assert.Equal(0, stats.FilterCountFusionHits);
        Assert.Equal(0, stats.FilterCountFusionFallbacks);
        Assert.Empty(stats.FallbackReasons);
    }

    public static TheoryData<string, string> OpenedBuiltinNameProviders() => new()
    {
        {
            "opened count",
            "Lib = { public count(collection) = 456 }\nUse = { open Lib\nIsEven = x mod 2 == 0\nrange(1, 10).filter(IsEven).count }\nUse"
        },
        {
            "opened filter",
            "Lib = { public filter(*source, predicate) = 123 }\nUse = { open Lib\nIsEven = x mod 2 == 0\nrange(1, 10).filter(IsEven).count }\nUse"
        },
    };

    [Theory]
    [MemberData(nameof(OpenedBuiltinNameProviders))]
    public void OpenedSameNamedProvider_PreservesOwnershipFirstBuiltinSelection(
        string form,
        string source)
    {
        // Ownership-first lookup reaches the directly owned prelude binding before
        // an opened provider at this scope. The optimizer must make the same
        // declaration choice, not conservatively treat the opened spelling as a
        // shadow. A forced-generic run is the semantic oracle for that precedence.
        Assert.False(string.IsNullOrEmpty(form));

        var observations = new EvaluationObservations();
        var diagnostics = new SequencePipelineDiagnostics();
        var (result, _) = Evaluator.RunCountedObserved(
            Program(source),
            sequenceDiagnostics: diagnostics,
            observations: observations);
        var genericResult = Evaluator.RunObserved(
            Program(source),
            new EvaluationObservations(),
            enableOptimizations: false);

        Assert.False(result.IsError);
        Assert.False(genericResult.IsError);
        Assert.Equal(genericResult.Value.ToAtoms(), result.Value.Value.ToAtoms());
        Assert.Equal([5m], result.Value.Value.ToAtoms());
        Assert.Equal(1, observations.SequencePipelineServiceConstructionCount);

        var stats = diagnostics.GetSnapshot();
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(0, stats.FilterCountFusionFallbacks);
        Assert.Empty(stats.FallbackReasons);
    }

    [Fact]
    public void DirectTryExecute_CompositionPreservesCallbackOrderAndCommitBoundary()
    {
        // The retained white-box entry must remain the exact composition of
        // TryRecognize + TryExecuteRecognized. All lookup-only eligibility
        // callbacks occur at depth zero; source evaluation is the first callback
        // inside the committed outer argument-evaluation level.
        var range = new Expr.Call(
            new Expr.Resolve("range"),
            [new Expr.Num(1), new Expr.Num(1)]);
        var filter = new Expr.DotCall(
            range,
            "filter",
            [new Expr.Resolve("P")]);
        var invocation = SequencePipelineInvocation.DotCall(new Expr.DotCall(filter, "count"));
        var predicate = new Algorithm.User(
            Parent: null,
            Parameters: [new ParameterDeclaration("x")],
            Opens: [],
            Properties: [],
            Output: [new Expr.Num(1)]);
        var budget = EvaluationBudget.Create(null);
        var ctx = Evaluator.EvalCtx.Empty with { Budget = budget };
        var callbacks = new List<string>();

        var services = new SequencePipelineEvaluationServices(
            GetDotCallLexicalBuiltinFallbackReason: (_, expectedBuiltin) =>
            {
                callbacks.Add($"dot:{expectedBuiltin}@{budget.CurrentDepth}");
                return null;
            },
            EvaluateDotReceiverIterationItems: _ =>
                throw new Xunit.Sdk.XunitException("generic source evaluation must not run for a direct range"),
            ResolveArgumentAlgorithms: _ =>
            {
                callbacks.Add($"resolve-args@{budget.CurrentDepth}");
                return EvalResult<IReadOnlyList<Algorithm>>.Ok([predicate]);
            },
            ResolveAlgorithm: _ =>
            {
                callbacks.Add($"resolve:range@{budget.CurrentDepth}");
                return EvalResult<Algorithm>.Ok(new Algorithm.Builtin(BuiltinId.@range));
            },
            EvaluateRangeCallArguments: (_, _, _) =>
            {
                callbacks.Add($"evaluate-range@{budget.CurrentDepth}");
                return EvalResult<Evaluator.InclusiveRange>.Ok(new Evaluator.InclusiveRange(1, 1));
            });

        var diagnostics = new SequencePipelineDiagnostics();
        var handled = SequencePipelineOptimizer.TryExecute(
            invocation,
            services,
            ctx,
            [],
            diagnostics,
            out var result);

        Assert.True(handled);
        Assert.False(result.IsError);
        Assert.Equal([1m], result.Value.Value.ToAtoms());
        Assert.Equal(
            [
                "dot:count@0",
                "dot:filter@0",
                "resolve-args@0",
                "resolve:range@0",
                "evaluate-range@1",
            ],
            callbacks);
        Assert.Equal(0, budget.CurrentDepth);
        Assert.Equal(1, diagnostics.GetSnapshot().FilterCountFusionHits);
    }
}
