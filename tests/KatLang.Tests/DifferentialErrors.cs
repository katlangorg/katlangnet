namespace KatLang.Tests;

// Supplementary Q-67 evidence, separate from the FORMAL-06 neutral observation.
public enum ErrorComparison { Comparable, Partial, CategoryOnly, HostOnly }

public sealed record SharedErrorPayload
{
    public string Kind { get; }
    public IReadOnlyList<string> Names { get; }
    public IReadOnlyList<int> Counts { get; }

    public SharedErrorPayload(string kind, IReadOnlyList<string> names, IReadOnlyList<int> counts)
    {
        Kind = kind;
        Names = Array.AsReadOnly(names.ToArray());
        Counts = Array.AsReadOnly(counts.ToArray());
    }

    public bool Equals(SharedErrorPayload? other) => other is not null
        && Kind == other.Kind && Names.SequenceEqual(other.Names) && Counts.SequenceEqual(other.Counts);
    public override int GetHashCode() => HashCode.Combine(Kind, Names.Count, Counts.Count);
    public override string ToString() => $"{Kind} names=[{string.Join(", ", Names)}] counts=[{string.Join(", ", Counts)}]";

    internal string Lean => "(some { kind := " + LeanAstEncoder.QuoteString(Kind)
        + ", names := [" + string.Join(", ", Names.Select(LeanAstEncoder.QuoteString))
        + "], counts := [" + string.Join(", ", Counts.Select(n => n.ToString(System.Globalization.CultureInfo.InvariantCulture))) + "] })";
}

public sealed record DifferentialError(string Category, ErrorComparison Comparison, SharedErrorPayload? Payload);

public static class DifferentialErrors
{
    private static DifferentialError Fields(string category, string kind, string[]? names = null,
        int[]? counts = null, bool partial = false) => new(category,
            partial ? ErrorComparison.Partial : ErrorComparison.Comparable,
            new SharedErrorPayload(kind, names ?? [], counts ?? []));
    private static DifferentialError Category(string category) => new(category, ErrorComparison.CategoryOnly, null);
    private static DifferentialError Host(string category) => new(category, ErrorComparison.HostOnly, null);

    // No rendered descriptions, diagnostic metadata, spans or contexts. Variadic minimum is
    // Lean's arityMismatch expected count (needCardinalityGate / NeedCallArityError).
    // The switch names every variant with no catch-all arm, so a new EvalError variant fails
    // the build here (CS8509 is an error) until its policy is decided.
    public static DifferentialError Observe(EvalError error)
    {
        while (error is EvalError.WithContext context) error = context.Inner;
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
            EvalError.TypeMismatch => Category("type"),
            EvalError.NoMatchingBranch => Category("branch"),
            EvalError.NotAnAlgorithm => Category("notAnAlgorithm"),
            EvalError.IllegalInOpen => Category("illegalInOpen"),
            EvalError.BadOpenForm => Category("badOpenForm"),
            EvalError.IllegalInEval => Category("illegalInEval"),
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

    private static string Exposure(PropertyExposure exposure) => exposure switch
    {
        PropertyExposure.Exported => "exported",
        PropertyExposure.LocalOnlyCapturedAncestorParameters => "captured",
        PropertyExposure.LocalOnlyConditionalAlgorithm => "conditional",
        _ => throw new ArgumentOutOfRangeException(nameof(exposure)),
    };

    internal static void RequireAgreement(string caseId, EvalError expected, EvalError actual)
    {
        var left = Observe(expected);
        var right = Observe(actual);
        if (left.Category != right.Category || left.Payload != right.Payload)
            throw new InvalidOperationException($"Error payload/route disagreement for '{caseId}': "
                + $"expected {Observe(expected)}, actual {Observe(actual)}.");
    }
}
