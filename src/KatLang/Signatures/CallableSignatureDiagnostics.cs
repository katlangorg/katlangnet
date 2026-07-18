namespace KatLang;

public sealed record CallableArityFacts(
    int MinTopLevelArgumentCount,
    int? MaxTopLevelArgumentCount,
    bool HasTopLevelVariadic,
    int TopLevelVariadicCount)
{
    public bool HasMultipleTopLevelVariadics => TopLevelVariadicCount > 1;

    public bool AcceptsArgumentCount(int argumentCount)
        => argumentCount >= MinTopLevelArgumentCount
            && (MaxTopLevelArgumentCount is null || argumentCount <= MaxTopLevelArgumentCount.Value);
}

public static class CallableSignatureDiagnostics
{
    public static CallableArityFacts GetArityFacts(CallableSignature signature)
    {
        var topLevelVariadicCount = signature.ParameterPatterns.Count(IsTopLevelVariadicCapture);
        var slotCount = signature.ParameterPatterns.Count;

        // A user item-supply signature — plain top-level captures containing one
        // rest (rest-only or a comma deconstruction) — binds the fixed captures and
        // lets the rest capture any number of items, so it accepts at least the
        // fixed-binding count and has no upper bound. Rest-only `G(x...)` is the
        // degenerate case with min 0. No-rest, sequence-value, and builtin sequence
        // signatures keep their exact top-level slot count.
        if (IsItemSupplySignature(signature, topLevelVariadicCount))
        {
            return new CallableArityFacts(
                slotCount - 1,
                MaxTopLevelArgumentCount: null,
                HasTopLevelVariadic: true,
                TopLevelVariadicCount: topLevelVariadicCount);
        }

        return new CallableArityFacts(
            slotCount,
            slotCount,
            topLevelVariadicCount > 0,
            topLevelVariadicCount);
    }

    // A top-level variadic signature consumes an item supply (a user-defined
    // shape such as `Inspect(items...)` or `Scale(values..., factor)`): the
    // fixed captures bind and the rest accepts any number of argument slots
    // (collected as one exact immutable list at binding time), so
    // min = fixed count and max is unbounded. Collection builtins are NOT
    // item-supply signatures — they use one fixed `collection` parameter.
    private static bool IsItemSupplySignature(CallableSignature signature, int topLevelVariadicCount)
        => topLevelVariadicCount == 1
            && signature.ParameterPatterns.Count >= 1
            && !signature.HasSequenceValueParameterPattern;

    public static int TopLevelVariadicIndex(CallableSignature signature)
    {
        for (var index = 0; index < signature.ParameterPatterns.Count; index++)
        {
            if (IsTopLevelVariadicCapture(signature.ParameterPatterns[index]))
                return index;
        }

        return -1;
    }

    public static string FormatExpectedSignature(CallableSignature signature)
        => signature.DisplayText;

    public static string FormatBadArity(CallableSignature signature, int actualArgumentCount)
        => $"Callable `{signature.DisplayText}` expects {FormatExpectedArgumentCount(GetArityFacts(signature))}, but was called with {FormatCount(actualArgumentCount, "argument")}.";

    public static string FormatMultipleTopLevelVariadics(CallableSignature signature)
        => $"Callable signature `{signature.DisplayText}` cannot contain more than one variadic parameter.";

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

    private static bool IsTopLevelVariadicCapture(ParameterPattern parameterPattern)
        => parameterPattern is CaptureParameterPattern { Kind: ParameterKind.Variadic };
}
