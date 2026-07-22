using System.Globalization;
using System.Text;

namespace KatLang.ParserFuzz;

/// <summary>
/// Stable feature string for one executed metamorphic case: what the campaign actually
/// exercised, in a form that is identical on every machine and every run.
///
/// <para>Contains only decoded parameters and classified outcomes. No object hash codes, no
/// memory addresses, no timings, and no source text — a family plus its decoded dimensions
/// identifies a template far more stably than the text it happens to generate — so two runs of
/// the same input always produce the same fingerprint and a corpus can be summarized by
/// counting them.</para>
/// </summary>
internal static class MetamorphicFingerprint
{
    internal static string Describe(MetamorphicExecution execution, MetamorphicMismatch? mismatch)
    {
        ArgumentNullException.ThrowIfNull(execution);

        var testCase = execution.Case;
        var parameters = testCase.Parameters;
        var definition = testCase.Definition;

        var text = new StringBuilder(256);
        text.Append("family=").Append(definition.Id);
        text.Append("|group=").Append(definition.Group);
        text.Append("|status=").Append(execution.Accepted ? "accepted" : "rejected");
        text.Append("|rejection=").Append(execution.Accepted ? "none" : execution.RejectionReason);
        text.Append("|precondition=").Append(testCase.Precondition.Satisfied ? "ok" : testCase.Precondition.Reason);

        // Family-specific dimensions: builtin/callback identity, receiver and nested-value shape,
        // suffix arity, consumer, projection, chain length.
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
        text.Append("|relation=").Append(testCase.SemanticRelation).Append('+').Append(testCase.OperationalRelation);
        text.Append("|left=").Append(SideFeature(execution.Left));
        text.Append("|right=").Append(SideFeature(execution.Right));
        // Whether the operational counters were comparable at all, so a campaign summary shows
        // how much of its coverage reached the work comparison rather than stopping at semantics.
        text.Append("|work=").Append(
            execution is { Left: { } left, Right: { } right }
                ? MetamorphicComparator.WorkIsComparable(left, right) ? "compared" : "partial"
                : "absent");
        text.Append("|semanticMismatch=").Append(ClassFeature(mismatch, MetamorphicMismatchClass.Semantic));
        text.Append("|resourceMismatch=").Append(ClassFeature(mismatch, MetamorphicMismatchClass.ResourceBoundary));
        text.Append("|operationalMismatch=").Append(ClassFeature(mismatch, MetamorphicMismatchClass.Operational));
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

    private static string ClassFeature(MetamorphicMismatch? mismatch, MetamorphicMismatchClass mismatchClass)
        => mismatch is not null && mismatch.Class == mismatchClass ? mismatch.Kind.ToString() : "none";

    private static string Signed(int value)
        => (value >= 0 ? "+" : "") + value.ToString(CultureInfo.InvariantCulture);
}
