namespace KatLang.ParserFuzz;

/// <summary>Everything one UTF-16 payload produced. Replay compares two of these.</summary>
internal sealed record Utf16Report(
    Utf16Case Case,
    Utf16Observation Observation,
    Utf16RelationOutcome Relations,
    string Fingerprint);

/// <summary>
/// The <c>KATLANG_FUZZ_MODE=utf16</c> target.
///
/// <para>The payload is not source text: it selects a trusted template and a named run of UTF-16
/// code units (or, in the two raw modes, builds the units from the payload tail), so ill-formed
/// UTF-16 — isolated surrogates above all — is representable, reproducible and reviewable, which
/// UTF-8 decoding of raw fuzz bytes can never be.</para>
///
/// <para>The goal is NOT to make difficult UTF-16 parse. Structured, deterministic rejection is a
/// perfectly good outcome. What must never happen is an unexpected exception, an out-of-range or
/// self-inconsistent span, a token that disagrees with the source it came from, unbounded or
/// position-stuck diagnostics, a non-deterministic result, or a silently normalized code unit.</para>
///
/// <para>Every violation — and every unexpected CLR exception — escapes to the fuzzing engine with
/// its original type and stack. Nothing here converts one into an ordinary diagnostic.</para>
/// </summary>
internal static class Utf16Invariants
{
    /// <summary>libFuzzer callback. Lets everything escape, by design.</summary>
    public static void Check(ReadOnlySpan<byte> payload) => _ = Run(payload);

    public static Utf16Report Run(ReadOnlySpan<byte> payload)
    {
        var phase = Utf16Phase.Build;
        return Run(payload, ref phase);
    }

    /// <summary>Runs every stage, advancing <paramref name="phase"/> before each so a thrown
    /// exception leaves it naming the stage that failed.</summary>
    public static Utf16Report Run(ReadOnlySpan<byte> payload, ref Utf16Phase phase)
    {
        phase = Utf16Phase.Build;
        var parameters = Utf16Decoder.Decode(payload);
        var testCase = Utf16SourceBuilder.Build(parameters);

        var observation = Utf16Executor.Execute(testCase, ref phase);

        phase = Utf16Phase.Determinism;
        Utf16Executor.CheckDeterminism(testCase.Source);

        var relations = Utf16Relations.Check(parameters, ref phase);

        return new Utf16Report(
            testCase,
            observation,
            relations,
            Utf16Fingerprint.Describe(testCase, observation, relations));
    }
}
