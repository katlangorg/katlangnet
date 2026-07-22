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
    /// Whether the sequence-pipeline optimizer can actually FUSE under one case's execution
    /// policy. The optimizer flag alone does not decide this: the runtime gate is
    ///
    /// <code>
    /// loopOptimize     = !budget.HasStepLimit
    /// sequenceOptimize = loopOptimize &amp;&amp; !budget.HasConfiguredStringLimit
    /// </code>
    ///
    /// <para>(<c>Evaluator.CreateRootCtx</c>), and <c>EvaluationBudget</c> sets
    /// <c>HasConfiguredStringLimit</c> whenever EITHER string limit was configured. So a
    /// configured string budget — however generous — or a configured step budget turns fusion
    /// off for the whole run even with optimizations requested.</para>
    ///
    /// <para>ONE place owns this rule, so a template, a relation selector, and a test cannot
    /// drift into three slightly different approximations of it. It is an eligibility upper
    /// bound, never a claim that a particular program WAS fused: a directional relation stays
    /// sound when fusion is merely possible, and the exact relation is claimed only where it is
    /// impossible.</para>
    /// </summary>
    internal static bool SequencePipelineFusionCanApply(bool enableOptimizations, EvaluationLimits? limits)
        => enableOptimizations && !DisablesSequencePipelineFusion(limits);

    /// <summary>The configured limits the runtime treats as fusion-disabling, in its own terms.</summary>
    internal static bool DisablesSequencePipelineFusion(EvaluationLimits? limits)
        => limits is not null
            && (limits.MaxSteps is not null                       // -> EvaluationBudget.HasStepLimit
                || limits.MaxStringLength is not null             // -> HasConfiguredStringLimit
                || limits.MaxMaterializedStringChars is not null);

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
            // Explicit limits comfortably above everything the pair needs: the run must behave
            // exactly like the default policy, which is what makes this mode worth generating.
            //
            // Only the ITEM budgets are configured. A configured string budget is fusion-DISABLING
            // regardless of how large it is (see SequencePipelineFusionCanApply), so setting one
            // here would quietly make "generous" a different execution policy from the default it
            // exists to mirror — the pair would still agree, but on the unfused numbers. The
            // dedicated CumulativeStrings and PerStringLength modes cover the string budgets, and
            // they are the modes where losing fusion is the point rather than an accident.
            var generousItems = checked(measurement.Items + GenerousHeadroom);
            return (new EvaluationLimits
            {
                MaxMaterializedItems = generousItems,
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
