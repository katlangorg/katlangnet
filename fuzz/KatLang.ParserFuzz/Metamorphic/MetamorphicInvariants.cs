using System.Globalization;
using System.Text;

namespace KatLang.ParserFuzz;

/// <summary>
/// Thrown when an executed pair violated a relation its case DECLARED. This is a finding
/// about the language implementation (or about the declared relation), not a harness fault —
/// harness faults throw <see cref="MetamorphicHarnessException"/>, and every other unexpected
/// exception is left alone so the fuzzing engine records it as a crash.
/// </summary>
internal sealed class MetamorphicMismatchException(string message) : Exception(message);

/// <summary>Everything one metamorphic execution produced, in replayable form.</summary>
internal sealed record MetamorphicRunReport(
    MetamorphicParameters Parameters,
    MetamorphicExecution Execution,
    MetamorphicMismatch? Mismatch,
    string RawInputHex,
    int RawInputLength)
{
    public bool Accepted => Execution.Accepted;

    public string RejectionReason => Execution.RejectionReason;

    public string Fingerprint => MetamorphicFingerprint.Describe(Execution, Mismatch);
}

/// <summary>
/// The operational-metamorphic fuzz target (<c>KATLANG_FUZZ_MODE=metamorphic</c>).
///
/// <para>Unlike the raw-parser, frontend, and evaluator targets, this one does not feed
/// arbitrary bytes to the language. It decodes them into parameters for a TRUSTED TEMPLATE,
/// instantiates a pair of programs whose equivalence is guaranteed by construction, runs both
/// with independent state, and compares them against the relations the case declared. A
/// difference is therefore evidence about the implementation rather than about the input.</para>
/// </summary>
internal static class MetamorphicInvariants
{
    /// <summary>How often the sampled A/B/A executor-isolation check runs (deterministic per input).</summary>
    private const uint IsolationSampleModulus = 32;

    /// <summary>Bytes of the original fuzz input echoed into a mismatch report.</summary>
    private const int RawPrefixBytes = 16;

    /// <summary>libFuzzer callback: every violation and every unexpected exception escapes.</summary>
    public static void Check(ReadOnlySpan<byte> input)
    {
        var report = Run(input);

        if (report.Mismatch is { } mismatch)
            throw new MetamorphicMismatchException(Describe(report, mismatch));

        // Sampled state-isolation regression on the executor itself: a run of one program must
        // never change a later observation of another. Sampled because it triples the work.
        if (report.Accepted && StableHash(input) % IsolationSampleModulus == 0)
        {
            var testCase = report.Execution.Case;
            MetamorphicExecutor.AssertIsolated(testCase.LeftSource, testCase.Limits, testCase.EnableOptimizations);
            MetamorphicExecutor.AssertIsolated(testCase.RightSource, testCase.Limits, testCase.EnableOptimizations);
        }
    }

    /// <summary>
    /// Decode → instantiate → execute → compare. The single path used by BOTH the fuzzing
    /// loop and deterministic replay, so a replayed seed cannot mean something different from
    /// what the campaign ran.
    /// </summary>
    internal static MetamorphicRunReport Run(ReadOnlySpan<byte> input)
    {
        var parameters = MetamorphicDecoder.Decode(input);
        var testCase = MetamorphicTemplates.Build(parameters);
        var execution = MetamorphicExecutor.Execute(testCase);

        var mismatch = execution is { Accepted: true, Left: { } left, Right: { } right }
            ? MetamorphicComparator.Compare(testCase, left, right)
            : null;

        // The canonical encoding alone reproduces the case; the raw prefix is echoed only when
        // something failed, so the fuzzing loop never pays for a diagnostic it does not use.
        var rawHex = mismatch is null ? "" : Hex(input[..Math.Min(input.Length, RawPrefixBytes)]);
        return new MetamorphicRunReport(parameters, execution, mismatch, rawHex, input.Length);
    }

    /// <summary>Full, deterministic reproduction report for one mismatch.</summary>
    internal static string Describe(MetamorphicRunReport report, MetamorphicMismatch mismatch)
    {
        ArgumentNullException.ThrowIfNull(report);
        ArgumentNullException.ThrowIfNull(mismatch);

        var testCase = report.Execution.Case;
        var text = new StringBuilder(1024);
        text.Append("Metamorphic relation violated: ").Append(mismatch.Headline).AppendLine();
        text.Append("  family:                 ").AppendLine(testCase.FamilyId);
        text.Append("  failed comparison:      ").Append(mismatch.Kind).Append(" (").Append(mismatch.Class).AppendLine(")");
        text.Append("  declared semantic:      ").AppendLine(testCase.SemanticRelation.ToString());
        text.Append("  declared operational:   ").AppendLine(testCase.OperationalRelation.ToString());
        text.Append("  precondition:           ")
            .Append(testCase.Precondition.Satisfied ? "satisfied" : "REJECTED")
            .Append(" (").Append(testCase.Precondition.Reason).AppendLine(")");
        text.Append("  case status:            ")
            .AppendLine(report.Accepted ? "accepted" : "rejected: " + report.RejectionReason);
        text.Append("  replay parameters:      ").AppendLine(report.Parameters.ToString());
        text.Append("  replay payload (hex):   ").AppendLine(report.Parameters.ToHex());
        text.Append("  raw fuzz input:         ")
            .Append(report.RawInputLength.ToString(CultureInfo.InvariantCulture)).Append(" byte(s), first ")
            .Append(Math.Min(report.RawInputLength, RawPrefixBytes).ToString(CultureInfo.InvariantCulture))
            .Append(": ").AppendLine(report.RawInputHex.Length == 0 ? "-" : report.RawInputHex);
        text.Append("  limits:                 ").AppendLine(testCase.LimitsText);
        text.Append("  optimizer policy:       ").AppendLine(testCase.EnableOptimizations ? "on" : "off");
        text.Append("  Lean-representable:     ")
            .AppendLine(testCase.LeanRepresentable
                ? "yes (each member's SEMANTICS; the operational relation is C#-only)"
                : "no");
        text.Append("  expected item total:    ")
            .AppendLine(testCase.ExpectedItemTotal.ToString(CultureInfo.InvariantCulture));
        text.Append("  left source:            ").AppendLine(Escape(testCase.LeftSource));
        text.Append("  right source:           ").AppendLine(Escape(testCase.RightSource));
        text.Append("  left semantic:          ").AppendLine(Describe(report.Execution.Left?.Semantic));
        text.Append("  right semantic:         ").AppendLine(Describe(report.Execution.Right?.Semantic));
        text.Append("  left operational:       ").AppendLine(report.Execution.Left?.ToString() ?? "-");
        text.Append("  right operational:      ").AppendLine(report.Execution.Right?.ToString() ?? "-");
        text.Append("  fingerprint:            ").AppendLine(report.Fingerprint);
        text.Append("  reproduce:              dotnet run --project fuzz\\KatLang.ParserFuzz -- metamorphic-replay --payload ")
            .AppendLine(report.Parameters.ToHex().Replace(" ", "", StringComparison.Ordinal));
        return text.ToString();
    }

    private static string Describe(MetamorphicSemanticObservation? observation) => observation?.ToString() ?? "-";

    private static string Escape(string source) => source.Replace("\n", "\\n", StringComparison.Ordinal);

    private static string Hex(ReadOnlySpan<byte> bytes)
    {
        var text = new StringBuilder(bytes.Length * 3);
        foreach (var value in bytes)
        {
            if (text.Length > 0) text.Append(' ');
            text.Append(value.ToString("x2", CultureInfo.InvariantCulture));
        }

        return text.ToString();
    }

    private static uint StableHash(ReadOnlySpan<byte> input)
    {
        uint hash = 2166136261;
        foreach (var value in input)
        {
            hash ^= value;
            hash *= 16777619;
        }

        return hash;
    }
}
