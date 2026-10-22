using System.Collections.Immutable;
using System.Globalization;
using System.Text;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>How much of one innermost error's structured payload is comparable (Q-67's policy).</summary>
internal enum MetamorphicErrorComparison
{
    /// <summary>Every field that identifies the error is in the payload.</summary>
    Comparable,

    /// <summary>A stable subset is in the payload; the rest (a callee name, ...) is not compared.</summary>
    Partial,

    /// <summary>Only the category: the variant's fields are descriptions, not structured data.</summary>
    CategoryOnly,

    /// <summary>A host resource or loader failure; its numeric payload is the resource observation's.</summary>
    HostOnly,
}

/// <summary>
/// The STRUCTURED fields of one innermost <see cref="EvalError"/> — never rendered text, spans,
/// diagnostic metadata or <c>WithContext</c> prose (SEM-2A).
///
/// <para>This is the ONE classification shared by two consumers, compiled into both the fuzz
/// target and the test assembly: Q-67's differential corpus (<c>DifferentialErrors.Observe</c> in
/// the test project maps it onto its public records unchanged) and the metamorphic comparator's
/// strict same-source error policy (<see cref="MetamorphicErrorPolicy.StrictSameSource"/>). The
/// switch names every variant with no catch-all arm, so a new <c>EvalError</c> variant fails the
/// test build (CS8509 is an error there) until its policy is decided.</para>
/// </summary>
internal sealed record MetamorphicErrorDetail(
    string Category,
    MetamorphicErrorComparison Comparison,
    string? Kind,
    ImmutableArray<string> Names,
    ImmutableArray<int> Counts)
{
    /// <summary>Unwraps every context frame and classifies the innermost error.</summary>
    internal static MetamorphicErrorDetail Observe(EvalError error)
    {
        ArgumentNullException.ThrowIfNull(error);
        while (error is EvalError.WithContext context) error = context.Inner;

        // No rendered descriptions, diagnostic metadata, spans or contexts. Variadic minimum is
        // Lean's arityMismatch expected count (needCardinalityGate / NeedCallArityError).
        return error switch
        {
            // The loop has eliminated this variant; it is named only to keep the switch exhaustive.
            EvalError.WithContext => throw new System.Diagnostics.UnreachableException(),
            // A non-initiating observation's internal pending marker (META-S3-0b) never leaves its
            // observation scope, so no run outcome can carry it.
            EvalError.ObservationPending => throw new System.Diagnostics.UnreachableException("internal observation marker"),
            EvalError.ArityMismatch e => Fields("arity", "arity", counts: [e.Expected, e.Actual]),
            EvalError.VariadicArityMismatch e => Fields("arity", "arity", counts: [e.ExpectedMinimum, e.Actual], partial: true),
            EvalError.BadArity => Fields("arity", "badArity"),
            EvalError.BranchArityMismatch e => Fields("arity", "branchArity", counts: [e.Expected, e.Actual], partial: true),
            EvalError.BranchOutputArityMismatch e => Fields("arity", "branchOutputArity", counts: [e.Expected, e.Actual], partial: true),
            EvalError.UnknownName e => Fields("unknownName", "unknownName", [e.Name]),
            EvalError.UnknownProperty e => Fields("unknownProperty", "unknownProperty", [e.PropertyName], partial: true),
            EvalError.NotPublicProperty e => Fields("notPublicProperty", "notPublicProperty", [e.PropertyName], partial: true),
            EvalError.LocalOnlyProperty e => Fields("localOnlyProperty", "localOnlyProperty",
                [e.PropertyName, Exposure(e.Exposure)], partial: true),
            EvalError.AmbiguousOpen e => Fields("ambiguousOpen", "ambiguousOpen", [e.Name], partial: true),
            EvalError.DuplicateProperty e => Fields("duplicateProperty", "duplicateProperty", [e.Name]),
            EvalError.UnresolvedImplicitParams e => Fields("unresolvedImplicitParams", "unresolvedImplicitParams", [.. e.ParamNames]),
            EvalError.BadIndex => Fields("index", "index"),
            EvalError.DivByZero => Fields("div0", "div0"),
            EvalError.DemandCycle => Fields("demandCycle", "demandCycle"),
            EvalError.DuplicateBranchPattern => Fields("duplicateBranchPattern", "duplicateBranchPattern"),
            EvalError.ExplicitParametersRequireOutput => Fields("explicitParamsRequireOutput", "explicitParamsRequireOutput"),
            EvalError.MissingOutput => Fields("missingOutput", "missingOutput"),
            EvalError.SpreadMissingOutput => Fields("spreadMissingOutput", "spreadMissingOutput"),
            EvalError.TypeMismatch => CategoryOnly("type"),
            EvalError.NoMatchingBranch => CategoryOnly("branch"),
            EvalError.NotAnAlgorithm => CategoryOnly("notAnAlgorithm"),
            EvalError.IllegalInOpen => CategoryOnly("illegalInOpen"),
            EvalError.BadOpenForm => CategoryOnly("badOpenForm"),
            EvalError.IllegalInEval => CategoryOnly("illegalInEval"),
            EvalError.EvaluationDepthExceeded => Host("evaluationDepthExceeded"),
            EvalError.EvaluationStepLimitExceeded => Host("evaluationStepLimitExceeded"),
            EvalError.EvaluationStackExhausted => Host("evaluationStackExhausted"),
            EvalError.CollectionSizeLimitExceeded => Host("collectionSizeLimitExceeded"),
            EvalError.MaterializationLimitExceeded => Host("materializationLimitExceeded"),
            EvalError.StringSizeLimitExceeded => Host("stringSizeLimitExceeded"),
            EvalError.StringMaterializationLimitExceeded => Host("stringMaterializationLimitExceeded"),
            EvalError.DisplayLengthLimitExceeded => Host("displayLengthLimitExceeded"),
            EvalError.AstDepthLimitExceeded => Host("astDepthLimitExceeded"),
            EvalError.AstCycleDetected => Host("astCycleDetected"),
            EvalError.ModuleRegionMaterializationFailed => Host("moduleRegionMaterializationFailed"),
        };
    }

    public bool Equals(MetamorphicErrorDetail? other) => other is not null
        && string.Equals(Category, other.Category, StringComparison.Ordinal)
        && Comparison == other.Comparison
        && string.Equals(Kind, other.Kind, StringComparison.Ordinal)
        && Names.SequenceEqual(other.Names, StringComparer.Ordinal)
        && Counts.SequenceEqual(other.Counts);

    public override int GetHashCode() => HashCode.Combine(Category, Comparison, Kind, Names.Length, Counts.Length);

    /// <summary>Unambiguous text: names are quoted with the structural identity's escaping.</summary>
    public override string ToString()
    {
        var text = new StringBuilder(48).Append(Category).Append('/').Append(Comparison);
        if (Kind is null) return text.ToString();

        text.Append(" kind=").Append(Kind).Append(" names=[");
        var name = 0;
        for (; name < Names.Length && text.Length < 200; name++)
        {
            if (name > 0) text.Append(", ");
            text.Append(MetamorphicStructuralIdentity.PreviewText(Names[name]));
        }
        if (name < Names.Length) text.Append("…(+").Append((Names.Length - name).ToString(CultureInfo.InvariantCulture)).Append(" names)");

        text.Append("] counts=[");
        var count = 0;
        for (; count < Counts.Length && text.Length < 220; count++)
        {
            if (count > 0) text.Append(", ");
            text.Append(Counts[count].ToString(CultureInfo.InvariantCulture));
        }
        if (count < Counts.Length) text.Append("…(+").Append((Counts.Length - count).ToString(CultureInfo.InvariantCulture)).Append(" counts)");

        return MetamorphicStructuralIdentity.Preview(text.Append(']').ToString());
    }

    private static MetamorphicErrorDetail Fields(
        string category, string kind, string[]? names = null, int[]? counts = null, bool partial = false)
        => new(category, partial ? MetamorphicErrorComparison.Partial : MetamorphicErrorComparison.Comparable,
            kind, [.. names ?? []], [.. counts ?? []]);

    private static MetamorphicErrorDetail CategoryOnly(string category)
        => new(category, MetamorphicErrorComparison.CategoryOnly, null, [], []);

    private static MetamorphicErrorDetail Host(string category)
        => new(category, MetamorphicErrorComparison.HostOnly, null, [], []);

    private static string Exposure(PropertyExposure exposure) => exposure switch
    {
        PropertyExposure.Exported => "exported",
        PropertyExposure.LocalOnlyCapturedAncestorParameters => "captured",
        PropertyExposure.LocalOnlyConditionalAlgorithm => "conditional",
        _ => throw new ArgumentOutOfRangeException(nameof(exposure)),
    };
}
