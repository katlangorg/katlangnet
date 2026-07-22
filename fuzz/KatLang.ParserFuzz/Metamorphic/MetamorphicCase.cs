using System.Globalization;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Relation families. A family names ONE trusted template plus the equivalence argument
/// that justifies comparing the pair it generates. Adding a family means adding a template
/// whose construction guarantees the declared relation — never a textual rewriting of an
/// arbitrary mutated program.
///
/// <para>Enum values are a compatibility surface: the Phase 1 family must stay registry index
/// 0, because a version-zero payload resolves there.</para>
/// </summary>
internal enum MetamorphicFamily
{
    /// <summary>
    /// Phase 1: the dotted collection call versus its ordinary receiver-first spelling
    /// (<c>count(range(1, N))</c> vs <c>range(1, N).count</c>). The dotted form is not an
    /// optimization of the ordinary form, it IS the ordinary form — <c>A.F(B)</c> means
    /// <c>F(A, B)</c> — so semantic AND exact operational equality are both justified.
    /// </summary>
    DottedCollectionCall,

    /// <summary>
    /// Phase 2 Group A: <c>F(receiver, suffix...)</c> against <c>receiver.F(suffix...)</c> over
    /// the trusted collection builtins and every receiver value kind.
    /// </summary>
    DottedCollectionBuiltin,

    /// <summary>
    /// Phase 2 Group B: the same rewrite for a USER-defined function, where the receiver
    /// expression's single evaluation is the operationally visible property.
    /// </summary>
    UserExtensionCall,

    /// <summary>
    /// Phase 2 Group C: a bounded dotted chain against the nested ordinary call the template
    /// builds structurally from the same link list.
    /// </summary>
    DottedChain,

    /// <summary>
    /// Phase 2 Group D: a direct builtin callback against a user wrapper with a provably
    /// equivalent callback projection.
    /// </summary>
    BuiltinCallbackWrapper,
}

/// <summary>The declared LANGUAGE-SEMANTIC relation between the two members of a pair.</summary>
internal enum MetamorphicSemanticRelation
{
    /// <summary>
    /// Both members produce the same stable semantic observation: success/failure, neutral
    /// structural value, emitted count, innermost stable error category and — where the
    /// payload is a machine-independent number — its structured payload.
    /// </summary>
    SemanticEqual,
}

/// <summary>
/// The declared OPERATIONAL relation between the two members of a pair.
///
/// <para><b>Every operational relation below carries one qualification.</b> Operational counters
/// are compared only when BOTH executions complete. When either side stops at a structured
/// resource limit, semantic outcome, resource-limit kind, and structured payload remain
/// comparable, but partial work counters are not: an aborted run's counters are the prefix
/// recorded at the abort point, and two equivalent forms may legitimately have done different
/// preparatory work before reaching the same limit. Ordinary (non-resource) semantic failures are
/// NOT exempt — their counters are compared exactly like a successful run's. The gate is
/// <see cref="MetamorphicComparator.WorkIsComparable"/>.</para>
/// </summary>
internal enum MetamorphicOperationalRelation
{
    /// <summary>
    /// Exact equality of materialized collection-item slots and materialized string UTF-16
    /// units, plus the same relevant resource-limit verdict. Deliberately NOT every counter:
    /// evaluation steps and peak dynamic depth are recorded for diagnostics only, because the
    /// two forms may legitimately differ in invocation accounting (a dotted zero-argument link
    /// charges one step and one depth level; a user wrapper adds a whole invocation).
    /// </summary>
    ExactMaterializationEqual,

    /// <summary>
    /// Everything <see cref="ExactMaterializationEqual"/> requires PLUS exact equality of
    /// evaluation steps and peak dynamic depth. Declared only where the repository already
    /// establishes that contract — currently the user-defined extension call, whose two
    /// spellings resolve to one and the same user invocation
    /// (<c>OperationalMetamorphicTests.UserExtensionCall_ChargesTheSameInBothForms</c>).
    /// </summary>
    ExactObservedWorkEqual,

    /// <summary>
    /// The RIGHT member never materializes MORE than the left. Declared where the right form is
    /// eligible for sequence-pipeline FUSION and the left form is not: a fused pipeline that
    /// materializes nothing legitimately charges less, and demanding equality would forbid the
    /// fusion the runtime documents. The inequality still catches the failure mode that matters —
    /// a dotted form doing MORE work than its ordinary equivalent, which is exactly how the
    /// duplicate dotted-receiver materialization defect presented.
    ///
    /// <para>Declared only where fusion is EFFECTIVELY eligible
    /// (<see cref="MetamorphicLimitPolicy.SequencePipelineFusionCanApply"/>: the optimizer flag
    /// plus the string and step budgets that switch the sequence-pipeline optimizer off).
    /// Measured: wherever fusion is ineligible the two forms agree exactly on all 144
    /// chain/receiver pairs, so those policies keep the exact check.</para>
    /// </summary>
    MaterializationNeverIncreases,
}

/// <summary>
/// Whether the template's own construction preconditions hold for one decoded parameter
/// point. A failed precondition is a REJECTED case, never a mismatch: the pair is not
/// compared at all, and the reason is reported.
/// </summary>
internal sealed record MetamorphicPrecondition(bool Satisfied, string Reason)
{
    public static readonly MetamorphicPrecondition Ok = new(true, "ok");

    public static MetamorphicPrecondition Rejected(string reason) => new(false, reason);
}

/// <summary>
/// One metamorphic testcase: a trusted template instantiation plus the execution policy and
/// the declared relations under which its two members must agree.
///
/// <para>This is deliberately not "one arbitrary source file". Equivalence is guaranteed by
/// how <see cref="LeftSource"/> and <see cref="RightSource"/> were CONSTRUCTED, so the
/// comparison is trustworthy without any semantic analysis of the generated text.</para>
///
/// <para>The declared <see cref="OperationalRelation"/> applies only when both executions
/// COMPLETE; see <see cref="MetamorphicOperationalRelation"/> for the resource-abort
/// qualification every operational relation carries.</para>
///
/// <para>Harness-internal; nothing here is public API.</para>
/// </summary>
internal sealed record MetamorphicCase(
    MetamorphicFamily Family,
    MetamorphicParameters Parameters,
    string LeftSource,
    string RightSource,
    MetamorphicSemanticRelation SemanticRelation,
    MetamorphicOperationalRelation OperationalRelation,
    EvaluationLimits? Limits,
    bool EnableOptimizations,
    MetamorphicPrecondition Precondition,
    bool LeanRepresentable,
    string Description)
{
    /// <summary>
    /// Item slots the template expects the generated collection to materialize, MEASURED from
    /// the left member's own run-scoped budget rather than modelled analytically. Used to place
    /// limits on, just below, and just above the real boundary, and by the deterministic tests;
    /// the fuzz target itself never asserts it, so the campaign stays a pair comparison rather
    /// than an oracle comparison.
    /// </summary>
    public long ExpectedItemTotal { get; init; }

    /// <summary>String UTF-16 units the left member was measured to materialize.</summary>
    public long ExpectedStringTotal { get; init; }

    /// <summary>Stable, machine-independent rendering of the effective limits.</summary>
    public string LimitsText => DescribeLimits(Limits);

    /// <summary>Family identifier used in seeds, reports, and fingerprints.</summary>
    public string FamilyId => FamilyIdOf(Family);

    /// <summary>The registry entry backing this case.</summary>
    public MetamorphicFamilyDefinition Definition => MetamorphicFamilyRegistry.Get(Family);

    internal static string FamilyIdOf(MetamorphicFamily family) => MetamorphicFamilyRegistry.Get(family).Id;

    internal static bool TryParseFamilyId(string text, out MetamorphicFamily family)
    {
        if (MetamorphicFamilyRegistry.TryGetById(text, out var definition))
        {
            family = definition.Family;
            return true;
        }

        family = default;
        return false;
    }

    internal static string DescribeLimits(EvaluationLimits? limits)
    {
        if (limits is null) return "default";

        var parts = new List<string>(4);
        if (limits.MaxMaterializedItems is { } cumulative)
            parts.Add("maxMaterializedItems=" + cumulative.ToString(CultureInfo.InvariantCulture));
        if (limits.MaxCollectionItems is { } perCollection)
            parts.Add("maxCollectionItems=" + perCollection.ToString(CultureInfo.InvariantCulture));
        if (limits.MaxMaterializedStringChars is { } cumulativeStrings)
            parts.Add("maxMaterializedStringChars=" + cumulativeStrings.ToString(CultureInfo.InvariantCulture));
        if (limits.MaxStringLength is { } perString)
            parts.Add("maxStringLength=" + perString.ToString(CultureInfo.InvariantCulture));
        return parts.Count == 0 ? "explicit(none)" : string.Join(",", parts);
    }
}
