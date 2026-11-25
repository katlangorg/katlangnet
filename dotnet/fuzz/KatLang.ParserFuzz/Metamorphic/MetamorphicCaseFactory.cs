namespace KatLang.ParserFuzz;

/// <summary>
/// Assembles a <see cref="MetamorphicCase"/> from a template's two generated sources.
///
/// <para>One place owns the parts every family shares — relation selection from the registry,
/// limit derivation from MEASURED totals, and the description — so a new template only has to
/// produce its pair and its preconditions.</para>
/// </summary>
internal static class MetamorphicCaseFactory
{
    internal static MetamorphicCase Create(
        MetamorphicParameters parameters,
        string leftSource,
        string rightSource,
        MetamorphicPrecondition precondition,
        string description)
    {
        var definition = parameters.Definition;

        // Calibrate against the left member's own run-scoped budget. This is a real evaluation
        // with default limits and fully independent state, discarded before either compared side
        // runs; nothing about it is simulated and no zero-valued configuration is used to infer
        // zero work.
        var measurement = MetamorphicLimitPolicy.Measure(leftSource, parameters.EnableOptimizations);
        var (limits, limitsNote) = MetamorphicLimitPolicy.Derive(parameters, measurement);

        return new MetamorphicCase(
            Family: parameters.Family,
            Parameters: parameters,
            LeftSource: leftSource,
            RightSource: rightSource,
            SemanticRelation: definition.SemanticRelation,
            // After Derive, so a policy-dependent family sees the limits it will really run with.
            OperationalRelation: definition.OperationalRelationFor(parameters, limits),
            Limits: limits,
            EnableOptimizations: parameters.EnableOptimizations,
            Precondition: precondition,
            LeanRepresentable: definition.LeanRepresentable,
            Description:
                $"{definition.Id}: {description}; limits {MetamorphicCase.DescribeLimits(limits)}{limitsNote}; " +
                $"optimizations {(parameters.EnableOptimizations ? "on" : "off")}")
        {
            ExpectedItemTotal = measurement.Items,
            ExpectedStringTotal = measurement.Strings,
        };
    }
}
