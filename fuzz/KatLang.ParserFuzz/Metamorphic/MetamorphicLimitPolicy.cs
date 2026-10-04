using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Derives a case's execution policy by MEASURING what the pair actually charges instead of
/// modelling it analytically.
///
/// <para>Phase 1 could compute its one family's item total from the range bounds. Phase 2's
/// families span every builtin, receiver kind, chain, and callback, so a closed-form model
/// would be a second implementation of the evaluator's accounting — exactly the kind of
/// simulated counter this harness must not grow. Instead the left member is run once with
/// DEFAULT limits and its own run-scoped budget is read (never a zero-valued configuration
/// used to infer zero work), and the limits are then placed relative to those real totals.</para>
///
/// <para>The calibration run is a fully independent run: its budget, cache, and front-end
/// state are its own, and it is discarded before either compared side executes.</para>
/// </summary>
internal static class MetamorphicLimitPolicy
{
    /// <summary>What one calibration run charged.</summary>
    internal readonly record struct Measurement(long Items, long Strings)
    {
        public static readonly Measurement None = new(0, 0);
    }

    /// <summary>Headroom added by <see cref="MetamorphicLimitMode.Generous"/>.</summary>
    private const long GenerousHeadroom = 1_000;

    /// <summary>Runs <paramref name="source"/> once under default limits to read its real totals.</summary>
    internal static Measurement Measure(string source, bool enableOptimizations)
        => MetamorphicExecutor.TryObserve(source, null, enableOptimizations, out var observation, out _)
            ? new Measurement(observation.MaterializedItems, observation.MaterializedStringChars)
            : Measurement.None;

    /// <summary>
    /// Whether the sequence-pipeline optimizer can FUSE under one case's execution policy:
    /// exactly when the optimizer flag requests it. LIMITS OBSERVE A RUN; THEY NEVER CHOOSE HOW IT
    /// RUNS (Q-09b, 2026-10-04): no configured limit selects an evaluation strategy, and a fused
    /// pipeline charges every budget exactly as the generic composition does, so the limits a case
    /// configures play no part here. (Until then <c>Evaluator.CreateRootCtx</c> switched fusion off
    /// whenever a step, string, or cumulative-item budget was configured, however generous, and
    /// this mirror reproduced that rule.)
    ///
    /// <para>ONE place owns this rule, so a template and a test cannot drift into two
    /// approximations of it. It is an eligibility statement, never a claim that a particular
    /// program WAS fused.</para>
    /// </summary>
    internal static bool SequencePipelineFusionCanApply(bool enableOptimizations)
        => enableOptimizations;

    /// <summary>
    /// Builds the limits for one case. Returns <c>null</c> for the default policy. KatLang
    /// rejects a non-positive item limit, so an offset that would ask for zero is clamped up and
    /// the clamp is reported rather than silently applied.
    /// </summary>
    internal static (EvaluationLimits? Limits, string Note) Derive(
        MetamorphicParameters parameters, Measurement measurement)
    {
        var mode = parameters.LimitMode;
        if (mode == MetamorphicLimitMode.Default) return (null, "");

        // The budget-law family derives one dimension's boundary per side; this shared policy
        // deliberately has no opinion there, and the case's own profiles carry the real limits.
        if (mode == MetamorphicLimitMode.FamilyDerived) return (null, "");

        if (mode == MetamorphicLimitMode.Generous)
        {
            // An explicit limit comfortably above everything the pair needs: the run must behave
            // exactly like the default policy, which is what makes this mode worth generating.
            //
            // Only the PER-COLLECTION ceiling is configured. (Every other budget was once
            // fusion-disabling however large it was; since Q-09b none selects a strategy, so the
            // choice is no longer forced. The dedicated CumulativeItems/CumulativeStrings/
            // PerStringLength modes cover those budgets, and the budget-law family's
            // in-budget-neutral law compares the unconfigured run against a generous limit of every
            // kind.)
            var generousItems = checked(measurement.Items + GenerousHeadroom);
            return (new EvaluationLimits
            {
                MaxCollectionItems = ToCollectionLimit(generousItems),
            }, "");
        }

        var clamped = false;
        long? cumulativeItems = null;
        int? perCollectionItems = null;
        long? cumulativeStrings = null;
        int? perStringLength = null;

        switch (mode)
        {
            case MetamorphicLimitMode.CumulativeItems:
                cumulativeItems = PlacePositive(measurement.Items, parameters.PrimaryOffset, ref clamped);
                break;
            case MetamorphicLimitMode.PerCollectionItems:
                perCollectionItems = ToCollectionLimit(
                    PlacePositive(measurement.Items, parameters.SecondaryOffset, ref clamped));
                break;
            case MetamorphicLimitMode.Both:
                cumulativeItems = PlacePositive(measurement.Items, parameters.PrimaryOffset, ref clamped);
                perCollectionItems = ToCollectionLimit(
                    PlacePositive(measurement.Items, parameters.SecondaryOffset, ref clamped));
                break;
            case MetamorphicLimitMode.CumulativeStrings:
                // The string budgets legally accept zero, so no clamping is needed there.
                cumulativeStrings = PlaceNonNegative(measurement.Strings, parameters.PrimaryOffset);
                break;
            case MetamorphicLimitMode.PerStringLength:
                perStringLength = ToStringLimit(PlaceNonNegative(measurement.Strings, parameters.SecondaryOffset));
                break;
        }

        var limits = new EvaluationLimits
        {
            MaxMaterializedItems = cumulativeItems,
            MaxCollectionItems = perCollectionItems,
            MaxMaterializedStringChars = cumulativeStrings,
            MaxStringLength = perStringLength,
        };

        return (limits, clamped ? " (offset clamped to the minimum legal limit)" : "");
    }

    private static long PlacePositive(long total, int offset, ref bool clamped)
    {
        var requested = checked(total + offset);
        if (requested >= 1) return requested;
        clamped = true;
        return 1;
    }

    private static long PlaceNonNegative(long total, int offset)
    {
        var requested = checked(total + offset);
        return requested < 0 ? 0 : requested;
    }

    private static int ToCollectionLimit(long value)
        => value >= EvaluationLimits.MaxSupportedCollectionItems
            ? EvaluationLimits.MaxSupportedCollectionItems
            : (int)value;

    private static int ToStringLimit(long value)
        => value >= EvaluationLimits.MaxSupportedStringLength
            ? EvaluationLimits.MaxSupportedStringLength
            : (int)value;
}
