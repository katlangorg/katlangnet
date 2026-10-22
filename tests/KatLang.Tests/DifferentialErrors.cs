using KatLang.ParserFuzz;

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
    // The ONE exhaustive field classification lives in the shared metamorphic source
    // (MetamorphicErrorDetail, compiled into this assembly and the fuzz target), so Q-67 and the
    // metamorphic strict same-source policy can never drift apart. This is a lossless mapping
    // onto Q-67's public records: no rendered descriptions, diagnostic metadata, spans or contexts.
    public static DifferentialError Observe(EvalError error)
    {
        var detail = MetamorphicErrorDetail.Observe(error);
        var comparison = detail.Comparison switch
        {
            MetamorphicErrorComparison.Comparable => ErrorComparison.Comparable,
            MetamorphicErrorComparison.Partial => ErrorComparison.Partial,
            MetamorphicErrorComparison.CategoryOnly => ErrorComparison.CategoryOnly,
            MetamorphicErrorComparison.HostOnly => ErrorComparison.HostOnly,
            _ => throw new ArgumentOutOfRangeException(nameof(error)),
        };

        return new DifferentialError(detail.Category, comparison,
            detail.Kind is null ? null : new SharedErrorPayload(detail.Kind, detail.Names, detail.Counts));
    }

    internal static void RequireAgreement(string caseId, EvalError expected, EvalError actual)
    {
        var left = Observe(expected);
        var right = Observe(actual);
        if (left.Category != right.Category || left.Payload != right.Payload)
            throw new InvalidOperationException($"Error payload/route disagreement for '{caseId}': "
                + $"expected {Observe(expected)}, actual {Observe(actual)}.");
    }
}
