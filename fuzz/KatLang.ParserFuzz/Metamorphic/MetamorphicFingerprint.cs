using System.Globalization;
using System.Text;

namespace KatLang.ParserFuzz;

/// <summary>
/// Stable feature string for one executed metamorphic case: what the campaign actually
/// exercised, in a form that is identical on every machine and every run.
///
/// <para>Contains only decoded parameters and classified outcomes. No object hash codes, no
/// memory addresses, no timings, no source text — so two runs of the same input always
/// produce the same fingerprint and a corpus can be summarized by counting them.</para>
/// </summary>
internal static class MetamorphicFingerprint
{
    internal static string Describe(MetamorphicExecution execution, MetamorphicMismatch? mismatch)
    {
        ArgumentNullException.ThrowIfNull(execution);

        var testCase = execution.Case;
        var parameters = testCase.Parameters;

        var text = new StringBuilder(160);
        text.Append("family=").Append(testCase.FamilyId);
        text.Append("|status=").Append(execution.Accepted ? "accepted" : "rejected:" + execution.RejectionReason);
        text.Append("|precondition=").Append(testCase.Precondition.Satisfied ? "ok" : testCase.Precondition.Reason);
        text.Append("|rangeStop=").Append(parameters.RangeStop.ToString(CultureInfo.InvariantCulture));
        text.Append("|cardinality=").Append(testCase.ExpectedItemTotal.ToString(CultureInfo.InvariantCulture));
        text.Append("|limitMode=").Append(parameters.LimitMode);
        text.Append("|cumulativeOffset=").Append(Signed(parameters.CumulativeOffset));
        text.Append("|perCollectionOffset=").Append(Signed(parameters.PerCollectionOffset));
        text.Append("|optimizer=").Append(parameters.EnableOptimizations ? "on" : "off");
        text.Append("|left=").Append(SideFeature(execution.Left));
        text.Append("|right=").Append(SideFeature(execution.Right));
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
