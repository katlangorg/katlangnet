using System.Globalization;
using System.Text;

namespace KatLang.ParserFuzz;

/// <summary>
/// Stable feature string for one executed metamorphic case: what the campaign actually
/// exercised, in a form that is identical on every machine and every run.
///
/// <para>Contains only decoded parameters and classified outcomes. No object hash codes, no
/// memory addresses, no timings, no thread or process ids, and no source text — a family plus its
/// decoded dimensions identifies a template far more stably than the text it happens to
/// generate — so two runs of the same input always produce the same fingerprint and a corpus can
/// be summarized by counting them.</para>
///
/// <para>Phase 3 adds the features its families are actually distinguished by: the two execution
/// profiles (surface, limits, optimizer policy), the run plan and execution order, the optimizer
/// path and cache profile each side was PROVEN to take, and the rendering projection. Everything
/// appended is derived from the case or from counts, so the stability rule is unchanged.</para>
/// </summary>
internal static class MetamorphicFingerprint
{
    internal static string Describe(MetamorphicExecution execution, MetamorphicMismatch? mismatch)
    {
        ArgumentNullException.ThrowIfNull(execution);

        var testCase = execution.Case;
        var parameters = testCase.Parameters;
        var definition = testCase.Definition;

        var text = new StringBuilder(384);
        text.Append("family=").Append(definition.Id);
        text.Append("|group=").Append(definition.Group);
        text.Append("|status=").Append(execution.Accepted ? "accepted" : "rejected");
        text.Append("|rejection=").Append(execution.Accepted ? "none" : execution.RejectionReason);
        text.Append("|precondition=").Append(testCase.Precondition.Satisfied ? "ok" : testCase.Precondition.Reason);

        // Family-specific dimensions: builtin/callback identity, receiver and nested-value shape,
        // suffix arity, consumer, projection, chain length, optimizer source, cache shape, surface
        // pair, budget law, resource dimension, isolation mode.
        if (definition.UsesLegacyRangeStop)
            text.Append("|rangeStop=").Append(parameters.RangeStop.ToString(CultureInfo.InvariantCulture));

        var variant = definition.DescribeVariant(parameters);
        if (variant.Length > 0) text.Append('|').Append(variant.Replace(' ', '|'));

        text.Append("|itemTotal=").Append(testCase.ExpectedItemTotal.ToString(CultureInfo.InvariantCulture));
        text.Append("|stringTotal=").Append(testCase.ExpectedStringTotal.ToString(CultureInfo.InvariantCulture));
        text.Append("|limitMode=").Append(parameters.LimitMode);
        text.Append("|primaryOffset=").Append(Signed(parameters.PrimaryOffset));
        text.Append("|secondaryOffset=").Append(Signed(parameters.SecondaryOffset));
        text.Append("|optimizer=").Append(parameters.EnableOptimizations ? "on" : "off");

        // Phase 3 execution shape. Identical to the Phase 1/2 values for every Phase 1/2 case:
        // both profiles are the observed evaluator surface under the case's shared policy, the
        // plan is sequential, and the order is left-first.
        text.Append("|leftProfile=").Append(testCase.LeftProfile);
        text.Append("|rightProfile=").Append(testCase.RightProfile);
        text.Append("|runPlan=").Append(MetamorphicExecutor.DescribeRunPlan(testCase));
        text.Append("|order=").Append(testCase.ExecutionOrder);
        text.Append("|boundaryStop=").Append(testCase.BoundaryStop);
        text.Append("|expectedResource=").Append(testCase.ExpectedResourceKind ?? "none");
        text.Append("|relation=").Append(testCase.SemanticRelation).Append('+').Append(testCase.OperationalRelation);
        text.Append("|left=").Append(SideFeature(execution.Left));
        text.Append("|right=").Append(SideFeature(execution.Right));
        text.Append("|leftOptimizerPath=").Append(OptimizerFeature(execution.Left));
        text.Append("|rightOptimizerPath=").Append(OptimizerFeature(execution.Right));
        text.Append("|leftCache=").Append(CacheFeature(execution.Left));
        text.Append("|rightCache=").Append(CacheFeature(execution.Right));
        text.Append("|leftRendering=").Append(RenderingFeature(execution.Left));
        text.Append("|rightRendering=").Append(RenderingFeature(execution.Right));
        // Whether the operational counters were comparable at all, so a campaign summary shows
        // how much of its coverage reached the work comparison rather than stopping at semantics.
        text.Append("|work=").Append(
            execution is { Left: { } left, Right: { } right }
                ? MetamorphicComparator.WorkIsComparable(left, right) ? "compared" : "partial"
                : "absent");
        text.Append("|semanticMismatch=").Append(ClassFeature(mismatch, MetamorphicMismatchClass.Semantic));
        text.Append("|resourceMismatch=").Append(ClassFeature(mismatch, MetamorphicMismatchClass.ResourceBoundary));
        text.Append("|operationalMismatch=").Append(ClassFeature(mismatch, MetamorphicMismatchClass.Operational));
        text.Append("|renderingMismatch=").Append(ClassFeature(mismatch, MetamorphicMismatchClass.Rendering));
        text.Append("|isolationMismatch=").Append(ClassFeature(mismatch, MetamorphicMismatchClass.StateIsolation));
        return text.ToString();
    }

    /// <summary>Outcome of one side, including which resource-limit variant stopped it.</summary>
    private static string SideFeature(MetamorphicOperationalObservation? observation)
    {
        if (observation is null) return "absent";
        var semantic = observation.Semantic;
        if (semantic.Outcome != "err") return "ok";
        return (semantic.IsResourceLimit ? "resource:" : "semantic:") + (semantic.ErrorCategory ?? "unknown");
    }

    /// <summary>The optimizer path one side was measured to take, or that none was observed.</summary>
    private static string OptimizerFeature(MetamorphicOperationalObservation? observation)
        => observation?.OptimizerEvidence?.Feature ?? "unobserved";

    /// <summary>The side's cache hit/miss/store profile, or that none was observed.</summary>
    private static string CacheFeature(MetamorphicOperationalObservation? observation)
        => observation?.CacheEvidence?.Feature ?? "unobserved";

    /// <summary>Which rendering projection the side produced, and whether it was bounded.</summary>
    private static string RenderingFeature(MetamorphicOperationalObservation? observation)
    {
        if (observation?.Projection is not { } projection) return "none";
        if (projection.RenderedText is null) return projection.RenderedProjection;
        return projection.RenderedProjection + ":" + (projection.RenderedLength <= projection.RenderedLimit
            ? "within-limit"
            : "over-limit");
    }

    private static string ClassFeature(MetamorphicMismatch? mismatch, MetamorphicMismatchClass mismatchClass)
        => mismatch is not null && mismatch.Class == mismatchClass ? mismatch.Kind.ToString() : "none";

    private static string Signed(int value)
        => (value >= 0 ? "+" : "") + value.ToString(CultureInfo.InvariantCulture);
}
