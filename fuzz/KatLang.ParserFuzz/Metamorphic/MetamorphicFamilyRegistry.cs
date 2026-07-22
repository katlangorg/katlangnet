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
            Description: "F(receiver, suffix...) against receiver.F(suffix...) for a trusted collection builtin",
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
            Description: "F(receiver, suffix...) against receiver.F(suffix...) for a user-defined function",
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
