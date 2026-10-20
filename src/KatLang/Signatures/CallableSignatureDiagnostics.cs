namespace KatLang;

internal sealed record CallableArityFacts(
    int MinTopLevelArgumentCount,
    int? MaxTopLevelArgumentCount,
    bool HasTopLevelCollecting,
    int TopLevelCollectingCount)
{
    public bool HasMultipleTopLevelCollectingCaptures => TopLevelCollectingCount > 1;

    public bool AcceptsArgumentCount(int argumentCount)
        => argumentCount >= MinTopLevelArgumentCount
            && (MaxTopLevelArgumentCount is null || argumentCount <= MaxTopLevelArgumentCount.Value);
}

internal static class CallableSignatureDiagnostics
{
    /// <summary>
    /// The arity the BINDER accepts for this signature's top-level parameter list,
    /// read from that list ALONE: its <see cref="PatternLevelArity"/>, the ONE supplied-slot
    /// rule the binder's own cardinality gate reads. Every pattern at this level
    /// consumes ONE supplied slot whatever it contains — a sequence-value group is one
    /// slot the binder opens afterwards — and a COLLECTING capture at this level consumes
    /// NONE, because it collects whatever the fixed prefix and suffix leave over (an empty
    /// leftover is the exact empty list). A collecting capture at this level therefore also
    /// lifts the upper bound; without one the count is exact.
    /// The decision is LEVEL-LOCAL: nested captures are never flattened into it, and a
    /// grouped pattern beside a collector does not make the collector fixed
    /// (<c>G((a, b), *rest)</c> is min 1, unbounded max — exactly what <c>G()</c>,
    /// <c>G((1, 2))</c>, and <c>G((1, 2), 3, 4)</c> do at run time).
    /// <see cref="PatternListBindingPlan"/> applies the same rule at every level.
    /// </summary>
    public static CallableArityFacts GetArityFacts(CallableSignature signature)
    {
        var parameterPatterns = signature.ParameterPatterns;
        // A shared implicit-signature template knows its top-level collecting count (FE-3).
        var topLevelCollectingCount = parameterPatterns is ImplicitSignatureTemplate template
            ? template.Facts.TopLevelCollectingCount
            : parameterPatterns.Count(IsTopLevelCollectingCapture);
        var arity = new PatternLevelArity(parameterPatterns.Count, HasCollectingCapture: topLevelCollectingCount > 0);

        return new CallableArityFacts(
            arity.Minimum,
            MaxTopLevelArgumentCount: arity.Maximum,
            HasTopLevelCollecting: arity.HasCollectingCapture,
            TopLevelCollectingCount: topLevelCollectingCount);
    }

    public static int TopLevelCollectingIndex(CallableSignature signature)
    {
        for (var index = 0; index < signature.ParameterPatterns.Count; index++)
        {
            if (IsTopLevelCollectingCapture(signature.ParameterPatterns[index]))
                return index;
        }

        return -1;
    }

    public static string FormatExpectedSignature(CallableSignature signature)
        => signature.DisplayText;

    /// <summary>
    /// The arity message of a call of <paramref name="signature"/>: the counts its own top-level
    /// patterns accept (<see cref="GetArityFacts"/>) — for a builtin its one registry signature,
    /// whose patterns ARE its arity contract (every builtin is fixed-arity since META-S3-3).
    /// </summary>
    public static string FormatBadArity(CallableSignature signature, int actualArgumentCount)
        => $"Callable `{signature.DisplayText}` expects {FormatExpectedArgumentCount(GetArityFacts(signature))}, but was called with {FormatCount(actualArgumentCount, "argument")}.";

    public static string FormatMultipleTopLevelCollectingCaptures(CallableSignature signature)
        => $"Callable signature `{signature.DisplayText}` cannot contain more than one collecting parameter.";

    public static string FormatExpectedArgumentCount(CallableArityFacts facts)
    {
        if (facts.MaxTopLevelArgumentCount is null)
        {
            return facts.MinTopLevelArgumentCount == 0
                ? "any number of arguments"
                : $"at least {FormatCount(facts.MinTopLevelArgumentCount, "argument")}";
        }

        if (facts.MinTopLevelArgumentCount == facts.MaxTopLevelArgumentCount.Value)
            return FormatCount(facts.MinTopLevelArgumentCount, "argument");

        return $"between {facts.MinTopLevelArgumentCount.ToString(System.Globalization.CultureInfo.InvariantCulture)} and {FormatCount(facts.MaxTopLevelArgumentCount.Value, "argument")}";
    }

    internal static string FormatExpectedArgumentCountWithoutNoun(CallableArityFacts facts)
    {
        if (facts.MaxTopLevelArgumentCount is null)
        {
            return facts.MinTopLevelArgumentCount == 0
                ? "any number of"
                : $"at least {facts.MinTopLevelArgumentCount.ToString(System.Globalization.CultureInfo.InvariantCulture)}";
        }

        if (facts.MinTopLevelArgumentCount == facts.MaxTopLevelArgumentCount.Value)
            return facts.MinTopLevelArgumentCount.ToString(System.Globalization.CultureInfo.InvariantCulture);

        return $"between {facts.MinTopLevelArgumentCount.ToString(System.Globalization.CultureInfo.InvariantCulture)} and {facts.MaxTopLevelArgumentCount.Value.ToString(System.Globalization.CultureInfo.InvariantCulture)}";
    }

    private static string FormatCount(int count, string singularNoun)
        => count == 1 ? $"1 {singularNoun}" : $"{count.ToString(System.Globalization.CultureInfo.InvariantCulture)} {singularNoun}s";

    private static bool IsTopLevelCollectingCapture(ParameterPattern parameterPattern)
        => parameterPattern is CaptureParameterPattern { Kind: ParameterKind.Collecting };
}
