namespace KatLang;

public sealed record CallableArityFacts(
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

public static class CallableSignatureDiagnostics
{
    public static CallableArityFacts GetArityFacts(CallableSignature signature)
    {
        var topLevelCollectingCount = signature.ParameterPatterns.Count(IsTopLevelCollectingCapture);
        var slotCount = signature.ParameterPatterns.Count;

        // A user item-supply signature — plain top-level captures containing one
        // collecting binding — binds the fixed captures and lets the
        // collecting binding capture any number of items, so it accepts at
        // least the fixed-binding count and has no upper bound. A single
        // collecting parameter `G(*x)` is the degenerate case with min 0.
        // Fixed-only, sequence-value, and builtin sequence signatures keep
        // their exact top-level slot count.
        if (IsItemSupplySignature(signature, topLevelCollectingCount))
        {
            return new CallableArityFacts(
                slotCount - 1,
                MaxTopLevelArgumentCount: null,
                HasTopLevelCollecting: true,
                TopLevelCollectingCount: topLevelCollectingCount);
        }

        return new CallableArityFacts(
            slotCount,
            slotCount,
            topLevelCollectingCount > 0,
            topLevelCollectingCount);
    }

    // A top-level collecting signature consumes an item supply (a user-defined
    // shape such as `Inspect(*items)` or `Scale(*values, factor)`): the
    // fixed captures bind and the collecting parameter accepts any number of
    // argument slots (collected as one exact immutable list at binding time),
    // so min = fixed count and max is unbounded. Collection builtins are NOT
    // item-supply signatures — they use one fixed `collection` parameter.
    private static bool IsItemSupplySignature(CallableSignature signature, int topLevelCollectingCount)
        => topLevelCollectingCount == 1
            && signature.ParameterPatterns.Count >= 1
            && !signature.HasSequenceValueParameterPattern;

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
