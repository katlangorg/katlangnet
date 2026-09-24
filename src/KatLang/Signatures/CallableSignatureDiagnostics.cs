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
    /// read from that list ALONE. The minimum is the binder's own rule
    /// (<see cref="ParameterPattern.MinimumSuppliedSlots"/>, which
    /// <c>BindParameterPatternList</c> itself enforces): every pattern at this level
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
        var topLevelCollectingCount = parameterPatterns.Count(IsTopLevelCollectingCapture);

        return new CallableArityFacts(
            ParameterPattern.MinimumSuppliedSlots(parameterPatterns),
            MaxTopLevelArgumentCount: topLevelCollectingCount > 0 ? null : parameterPatterns.Count,
            HasTopLevelCollecting: topLevelCollectingCount > 0,
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
