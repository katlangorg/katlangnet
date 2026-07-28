using System.Collections.Immutable;

namespace KatLang.ParserFuzz;

/// <summary>
/// Everything the harness needs to know about ONE trusted relation family. Adding a family
/// means adding a definition here plus its template — never a new switch arm scattered through
/// the decoder, executor, comparator, or fingerprint.
/// </summary>
internal sealed record MetamorphicFamilyDefinition(
    MetamorphicFamily Family,
    string Id,
    string Group,
    ImmutableArray<MetamorphicLimitMode> SupportedLimitModes,
    bool SupportsOptimizerPolicy,
    bool UsesLegacyRangeStop,
    ImmutableArray<int> ExtraDimensionSizes,
    MetamorphicSemanticRelation SemanticRelation,
    MetamorphicOperationalRelation OperationalRelation,
    bool LeanRepresentable,
    string Description,
    Func<MetamorphicParameters, MetamorphicParameters> Normalize,
    Func<MetamorphicParameters, MetamorphicPrecondition> ValidatePreconditions,
    Func<MetamorphicParameters, MetamorphicCase> Build,
    Func<MetamorphicParameters, string> DescribeVariantCore,
    Func<MetamorphicParameters, EvaluationLimits?, MetamorphicOperationalRelation>? SelectOperationalRelation = null)
{
    /// <summary>Appended family-specific dimensions (bytes 6+).</summary>
    public int ExtraDimensionCount => ExtraDimensionSizes.Length;

    /// <summary>
    /// The operational relation for ONE case. Usually the family's headline
    /// <see cref="OperationalRelation"/>, but a family whose two spellings differ in
    /// FUSION eligibility declares a policy-dependent relation instead — requiring equality
    /// where fusion cannot apply and an inequality where it can.
    ///
    /// <para>The DERIVED limits are part of that decision, not just the optimizer flag: a
    /// configured string or step budget disables the sequence-pipeline optimizer no matter how
    /// generous it is, so a case carrying one is back in exact-equality territory. That is why
    /// this takes the limits the case will actually run with.</para>
    /// </summary>
    public MetamorphicOperationalRelation OperationalRelationFor(
        MetamorphicParameters parameters, EvaluationLimits? limits)
        => SelectOperationalRelation?.Invoke(parameters, limits) ?? OperationalRelation;

    /// <summary>Total payload bytes one case of this family occupies.</summary>
    public int PayloadLength => MetamorphicParameters.CommonPayloadLength + ExtraDimensionCount;

    /// <summary>Stable, machine-independent description of this family's own dimensions.</summary>
    public string DescribeVariant(MetamorphicParameters parameters) => DescribeVariantCore(parameters);
}

/// <summary>
/// The registry of trusted relation families.
///
/// <para>Ordering is a compatibility surface: index 0 MUST stay the Phase 1 family, because a
/// version-zero (six-byte-or-shorter) payload always resolves to it. Appending new families is
/// safe; reordering or removing one is not.</para>
/// </summary>
internal static class MetamorphicFamilyRegistry
{
    private static readonly ImmutableArray<MetamorphicLimitMode> ItemLimitModes =
    [
        MetamorphicLimitMode.Default,
        MetamorphicLimitMode.CumulativeItems,
        MetamorphicLimitMode.PerCollectionItems,
        MetamorphicLimitMode.Both,
    ];

    private static readonly ImmutableArray<MetamorphicLimitMode> AllLimitModes =
    [
        MetamorphicLimitMode.Default,
        MetamorphicLimitMode.CumulativeItems,
        MetamorphicLimitMode.PerCollectionItems,
        MetamorphicLimitMode.Both,
        MetamorphicLimitMode.CumulativeStrings,
        MetamorphicLimitMode.PerStringLength,
        MetamorphicLimitMode.Generous,
    ];

    private static readonly ImmutableArray<MetamorphicFamilyDefinition> Definitions =
    [
        // ── Phase 1 (index 0 — frozen: version-zero payloads resolve here) ──────────
        new(
            Family: MetamorphicFamily.DottedCollectionCall,
            Id: "dotted-collection-call",
            Group: "dotted-builtin",
            // Frozen at the Phase 1 four-mode table so byte 2 keeps its exact old meaning.
            SupportedLimitModes: ItemLimitModes,
            SupportsOptimizerPolicy: true,
            UsesLegacyRangeStop: true,
            ExtraDimensionSizes: [],
            SemanticRelation: MetamorphicSemanticRelation.SemanticEqual,
            OperationalRelation: MetamorphicOperationalRelation.ExactMaterializationEqual,
            LeanRepresentable: true,
            Description: "count(range(1, N)) against range(1, N).count",
            Normalize: static parameters => parameters,
            ValidatePreconditions: MetamorphicTemplates.ValidateRangeCount,
            Build: MetamorphicTemplates.BuildRangeCount,
            DescribeVariantCore: static _ => ""),

        // ── Group A ────────────────────────────────────────────────────────────────
        new(
            Family: MetamorphicFamily.DottedCollectionBuiltin,
            Id: "dotted-collection-builtin",
            Group: "dotted-builtin",
            SupportedLimitModes: AllLimitModes,
            SupportsOptimizerPolicy: true,
            UsesLegacyRangeStop: false,
            // builtin, receiver shape, suffix variant
            ExtraDimensionSizes: [MetamorphicTables.Builtins.Length, MetamorphicTables.ReceiverShapes.Length, 6],
            SemanticRelation: MetamorphicSemanticRelation.SemanticEqual,
            OperationalRelation: MetamorphicOperationalRelation.ExactMaterializationEqual,
            LeanRepresentable: true,
            Description: "F(receiver, suffix.spread) against receiver.F(suffix.spread) for a trusted collection builtin",
            Normalize: MetamorphicDottedBuiltinTemplate.Normalize,
            ValidatePreconditions: MetamorphicDottedBuiltinTemplate.Validate,
            Build: MetamorphicDottedBuiltinTemplate.Build,
            DescribeVariantCore: MetamorphicDottedBuiltinTemplate.DescribeVariant),

        // ── Group B ────────────────────────────────────────────────────────────────
        new(
            Family: MetamorphicFamily.UserExtensionCall,
            Id: "user-extension-call",
            Group: "dotted-user",
            SupportedLimitModes: AllLimitModes,
            SupportsOptimizerPolicy: true,
            UsesLegacyRangeStop: false,
            // body template, receiver shape, suffix variant
            ExtraDimensionSizes: [MetamorphicUserExtensionTemplate.BodyCount, MetamorphicTables.ReceiverShapes.Length, 6],
            SemanticRelation: MetamorphicSemanticRelation.SemanticEqual,
            // The repository already establishes exact WORK equality for this pair
            // (OperationalMetamorphicTests.UserExtensionCall_ChargesTheSameInBothForms asserts
            // EvaluationSteps). The committed sweep keeps it honest: every accepted point of this
            // family's own body x receiver x suffix space is checked against this relation by
            // MetamorphicPhase2FamilyTests.UserExtensionCall_AgreesOnExactWorkAtEveryParameterPoint.
            OperationalRelation: MetamorphicOperationalRelation.ExactObservedWorkEqual,
            LeanRepresentable: true,
            Description: "F(receiver, suffix.spread) against receiver.F(suffix.spread) for a user-defined function",
            Normalize: MetamorphicUserExtensionTemplate.Normalize,
            ValidatePreconditions: MetamorphicUserExtensionTemplate.Validate,
            Build: MetamorphicUserExtensionTemplate.Build,
            DescribeVariantCore: MetamorphicUserExtensionTemplate.DescribeVariant),

        // ── Group C ────────────────────────────────────────────────────────────────
        new(
            Family: MetamorphicFamily.DottedChain,
            Id: "dotted-chain",
            Group: "dotted-chain",
            SupportedLimitModes: AllLimitModes,
            SupportsOptimizerPolicy: true,
            UsesLegacyRangeStop: false,
            // chain template, receiver shape
            ExtraDimensionSizes: [MetamorphicChainTemplate.ChainCount, MetamorphicTables.ReceiverShapes.Length],
            SemanticRelation: MetamorphicSemanticRelation.SemanticEqual,
            // Headline relation; the selector below weakens it to a directional one exactly
            // where sequence-pipeline fusion can apply to the dotted spelling.
            OperationalRelation: MetamorphicOperationalRelation.ExactMaterializationEqual,
            LeanRepresentable: true,
            Description: "a bounded dotted chain against its structurally built nested ordinary form",
            Normalize: MetamorphicChainTemplate.Normalize,
            ValidatePreconditions: MetamorphicChainTemplate.Validate,
            Build: MetamorphicChainTemplate.Build,
            DescribeVariantCore: MetamorphicChainTemplate.DescribeVariant,
            SelectOperationalRelation: MetamorphicChainTemplate.SelectOperationalRelation),

        // ── Group D ────────────────────────────────────────────────────────────────
        new(
            Family: MetamorphicFamily.BuiltinCallbackWrapper,
            Id: "builtin-callback-wrapper",
            Group: "callback-wrapper",
            SupportedLimitModes: AllLimitModes,
            SupportsOptimizerPolicy: true,
            UsesLegacyRangeStop: false,
            // consumer, callback builtin, input shape, wrapper projection
            ExtraDimensionSizes:
            [
                MetamorphicTables.CallbackConsumers.Length,
                MetamorphicTables.Builtins.Length,
                MetamorphicTables.CallbackInputShapes.Length,
                MetamorphicTables.WrapperProjections.Length,
            ],
            SemanticRelation: MetamorphicSemanticRelation.SemanticEqual,
            // The wrapper is an extra user invocation, so steps and depth legitimately differ.
            OperationalRelation: MetamorphicOperationalRelation.ExactMaterializationEqual,
            LeanRepresentable: true,
            Description: "a direct builtin callback against an equivalent user wrapper",
            Normalize: MetamorphicCallbackWrapperTemplate.Normalize,
            ValidatePreconditions: MetamorphicCallbackWrapperTemplate.Validate,
            Build: MetamorphicCallbackWrapperTemplate.Build,
            DescribeVariantCore: MetamorphicCallbackWrapperTemplate.DescribeVariant),

        // ── Phase 3 Group A ────────────────────────────────────────────────────────
        new(
            Family: MetamorphicFamily.OptimizerGenericParity,
            Id: "optimizer-generic-parity",
            Group: "optimizer",
            SupportedLimitModes: MetamorphicOptimizerTemplate.LimitModes,
            // The family FIXES both policies (optimized left, generic right), so byte 5 has no
            // meaning here and is normalized away rather than silently selecting one of them.
            SupportsOptimizerPolicy: false,
            UsesLegacyRangeStop: false,
            // source template, execution order
            ExtraDimensionSizes: [MetamorphicOptimizerTemplate.SourceCount, MetamorphicOptimizerTemplate.Orders.Length],
            SemanticRelation: MetamorphicSemanticRelation.SemanticEqual,
            // The optimizers exist to do LESS. Equality would forbid them; the inequality still
            // catches an optimized path that costs more than the generic one it replaced.
            OperationalRelation: MetamorphicOperationalRelation.WorkNeverIncreases,
            LeanRepresentable: true,
            Description: "one source with optimizations enabled against the same source with them disabled",
            Normalize: MetamorphicOptimizerTemplate.Normalize,
            ValidatePreconditions: MetamorphicOptimizerTemplate.Validate,
            Build: MetamorphicOptimizerTemplate.Build,
            DescribeVariantCore: MetamorphicOptimizerTemplate.DescribeVariant),

        // ── Phase 3 Group B ────────────────────────────────────────────────────────
        new(
            Family: MetamorphicFamily.CachedPropertyReuse,
            Id: "cached-property-reuse",
            Group: "cache",
            SupportedLimitModes: MetamorphicCacheTemplate.LimitModes,
            SupportsOptimizerPolicy: true,
            UsesLegacyRangeStop: false,
            // value/use template, reuse count, execution order
            ExtraDimensionSizes:
            [
                MetamorphicCacheTemplate.SourceCount,
                MetamorphicCacheTemplate.ReuseCounts.Length,
                MetamorphicCacheTemplate.Orders.Length,
            ],
            SemanticRelation: MetamorphicSemanticRelation.SemanticEqual,
            OperationalRelation: MetamorphicOperationalRelation.WorkNeverIncreases,
            LeanRepresentable: true,
            Description: "a reused zero-argument property against the independently rebuilt form",
            Normalize: MetamorphicCacheTemplate.Normalize,
            ValidatePreconditions: MetamorphicCacheTemplate.Validate,
            Build: MetamorphicCacheTemplate.Build,
            DescribeVariantCore: MetamorphicCacheTemplate.DescribeVariant),

        // ── Phase 3 Group C ────────────────────────────────────────────────────────
        new(
            Family: MetamorphicFamily.EntryPointParity,
            Id: "entry-point-parity",
            Group: "entry-point",
            SupportedLimitModes: MetamorphicEntryPointTemplate.LimitModes,
            // Only the observed evaluator entry point accepts an optimizer policy; every other
            // surface runs the production default, so the family fixes it ON.
            SupportsOptimizerPolicy: false,
            UsesLegacyRangeStop: false,
            // source template, surface pair, execution order
            ExtraDimensionSizes:
            [
                MetamorphicEntryPointTemplate.SourceCount,
                MetamorphicEntryPointTemplate.PairCount,
                MetamorphicEntryPointTemplate.Orders.Length,
            ],
            SemanticRelation: MetamorphicSemanticRelation.SameStructuredOutcome,
            // Overridden per case: counters are claimed only when BOTH surfaces hand back a budget.
            OperationalRelation: MetamorphicOperationalRelation.NotCompared,
            LeanRepresentable: true,
            Description: "one source through two runtime entry points, compared on their shared facets",
            Normalize: MetamorphicEntryPointTemplate.Normalize,
            ValidatePreconditions: MetamorphicEntryPointTemplate.Validate,
            Build: MetamorphicEntryPointTemplate.Build,
            DescribeVariantCore: MetamorphicEntryPointTemplate.DescribeVariant,
            SelectOperationalRelation: MetamorphicEntryPointTemplate.SelectOperationalRelation),

        // ── Phase 3 Group D ────────────────────────────────────────────────────────
        new(
            Family: MetamorphicFamily.BudgetLaw,
            Id: "budget-law",
            Group: "budget",
            // The family derives both sides' limits itself; the shared limit policy has no say.
            SupportedLimitModes: MetamorphicBudgetLawTemplate.LimitModes,
            SupportsOptimizerPolicy: false,
            UsesLegacyRangeStop: false,
            // source template, law, resource dimension, isolation mode
            ExtraDimensionSizes:
            [
                MetamorphicBudgetLawTemplate.SourceCount,
                MetamorphicBudgetLawTemplate.Laws.Length,
                MetamorphicBudgetLawTemplate.Dimensions.Length,
                MetamorphicBudgetLawTemplate.IsolationModes.Length,
            ],
            // Both are overridden per case: each law declares its own relation.
            SemanticRelation: MetamorphicSemanticRelation.SemanticEqual,
            OperationalRelation: MetamorphicOperationalRelation.NotCompared,
            LeanRepresentable: true,
            Description: "resource-budget laws: boundary sweeps, neutrality, failed reservations, run isolation",
            Normalize: MetamorphicBudgetLawTemplate.Normalize,
            ValidatePreconditions: MetamorphicBudgetLawTemplate.Validate,
            Build: MetamorphicBudgetLawTemplate.Build,
            DescribeVariantCore: MetamorphicBudgetLawTemplate.DescribeVariant),

        // ── Group E ────────────────────────────────────────────────────────────────
        new(
            Family: MetamorphicFamily.SpreadSpellingParity,
            Id: "spread-spelling-parity",
            Group: "spread-spelling",
            SupportedLimitModes: AllLimitModes,
            SupportsOptimizerPolicy: true,
            UsesLegacyRangeStop: false,
            // spread-slot context, operand shape
            ExtraDimensionSizes:
            [
                MetamorphicSpreadSpellingTemplate.ContextCount,
                MetamorphicTables.ReceiverShapes.Length,
            ],
            SemanticRelation: MetamorphicSemanticRelation.SemanticEqual,
            // `spread(X)` and `X.spread` lower to the SAME SequenceSpread node at parse
            // time, so the two members are the same program modulo source spans: parse
            // eligibility, values, structured errors, limit classifications, AND charged
            // evaluation work must all agree exactly.
            OperationalRelation: MetamorphicOperationalRelation.ExactObservedWorkEqual,
            LeanRepresentable: true,
            Description: "spread(X) against X.spread: both spellings of the spread intrinsic lower to one node",
            Normalize: MetamorphicSpreadSpellingTemplate.Normalize,
            ValidatePreconditions: MetamorphicSpreadSpellingTemplate.Validate,
            Build: MetamorphicSpreadSpellingTemplate.Build,
            DescribeVariantCore: MetamorphicSpreadSpellingTemplate.DescribeVariant),
    ];

    static MetamorphicFamilyRegistry()
    {
        if (Definitions[0].Family != MetamorphicFamily.DottedCollectionCall)
            throw new MetamorphicHarnessException("Registry index 0 must stay the Phase 1 family; version-zero payloads resolve there.");

        var ids = new HashSet<string>(StringComparer.Ordinal);
        var families = new HashSet<MetamorphicFamily>();
        foreach (var definition in Definitions)
        {
            if (!ids.Add(definition.Id))
                throw new MetamorphicHarnessException($"Duplicate metamorphic family id '{definition.Id}'.");
            if (!families.Add(definition.Family))
                throw new MetamorphicHarnessException($"Duplicate metamorphic family '{definition.Family}'.");
            if (definition.ExtraDimensionCount > MetamorphicParameters.MaxExtraDimensions)
                throw new MetamorphicHarnessException($"Family '{definition.Id}' declares too many appended dimensions.");
            foreach (var size in definition.ExtraDimensionSizes)
            {
                if (size is < 1 or > byte.MaxValue + 1)
                    throw new MetamorphicHarnessException($"Family '{definition.Id}' declares an unusable dimension size {size}.");
            }

            if (definition.SupportedLimitModes.Length is < 1 or > byte.MaxValue + 1)
                throw new MetamorphicHarnessException($"Family '{definition.Id}' declares no usable limit modes.");
        }
    }

    /// <summary>Every registered family, in payload order.</summary>
    internal static ImmutableArray<MetamorphicFamilyDefinition> All => Definitions;

    /// <summary>The definition for a registered family; unregistered families fail loudly.</summary>
    internal static MetamorphicFamilyDefinition Get(MetamorphicFamily family)
    {
        foreach (var definition in Definitions)
        {
            if (definition.Family == family) return definition;
        }

        throw new ArgumentOutOfRangeException(
            nameof(family), family, "No template is registered for this relation family.");
    }

    /// <summary>Looks a family up by its stable identifier (seed metadata, reports).</summary>
    internal static bool TryGetById(string id, out MetamorphicFamilyDefinition definition)
    {
        foreach (var candidate in Definitions)
        {
            if (string.Equals(candidate.Id, id, StringComparison.Ordinal))
            {
                definition = candidate;
                return true;
            }
        }

        definition = null!;
        return false;
    }
}
