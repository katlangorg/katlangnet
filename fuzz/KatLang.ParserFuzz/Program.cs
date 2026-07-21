using System.Text;
using KatLang;
using SharpFuzz;

namespace KatLang.ParserFuzz;

/// <summary>
/// Coverage-guided fuzzing harness for the raw KatLang parser.
///
/// Target: <c>Parser.ParseSyntax(source)</c> — the raw syntax boundary, BEFORE any
/// front-end elaboration (load elaboration, parameter detection, implicit-argument
/// resolution). We deliberately do NOT fuzz <c>Parser.Parse</c>, the evaluator,
/// module loading, or any network path.
///
/// Two modes:
///   * no args           -> libFuzzer mode (Fuzzer.LibFuzzer.Run), driven by the
///                          native libfuzzer-dotnet driver.
///   * one or more paths -> deterministic replay mode: parse each file/dir once
///                          with the invariants enabled and NO fuzzing loop. Used
///                          to reproduce and triage findings, and to smoke-test the
///                          harness + seed corpus on any platform.
/// </summary>
internal static class Program
{
    private static int Main(string[] args)
    {
        // Phase-2 depth characterization subcommands (process-isolated). Kept
        // separate from replay so a probe never collides with a corpus path.
        if (args.Length > 0 && args[0] == "probe-child")
            return DepthProbe.RunChild(args);   // dangerous parse in an isolated child
        if (args.Length > 0 && args[0] == "probe")
            return DepthProbe.RunParent(args);  // coordinator: exp+binary search
        if (args.Length > 0 && args[0] == "frontend-replay")
            return FrontEndReplay.Run(args);    // Phase-3 phase-aware frontend replay

        if (args.Length > 0)
            return Replay.Run(args);            // raw-parser replay (Phase 1)

        // libFuzzer mode. The delegate must let every unexpected exception, stack
        // overflow, hang, and invariant violation escape so the fuzzing engine records
        // them as crashes. KATLANG_FUZZ_MODE selects the target: default (unset) is the
        // raw parser — UNCHANGED and never replaced — and "frontend" fuzzes the default
        // elaborated pipeline (FrontEndPipeline.Process, no downloader).
        if (string.Equals(Environment.GetEnvironmentVariable("KATLANG_FUZZ_MODE"), "frontend", StringComparison.OrdinalIgnoreCase))
        {
            Fuzzer.LibFuzzer.Run(static bytes => FrontEndInvariants.Check(DecodeSource(bytes)));
        }
        else
        {
            Fuzzer.LibFuzzer.Run(static bytes =>
            {
                var source = DecodeSource(bytes);
                FuzzInvariants.Check(source, Parser.ParseSyntax(source));
            });
        }

        return 0;
    }

    /// <summary>
    /// Decodes arbitrary fuzzer bytes into a KatLang source string. UTF-8 is the
    /// source encoding; invalid byte sequences decode to U+FFFD (a perfectly valid
    /// piece of fuzz input) rather than throwing, so decoding never masks a parser
    /// defect behind a harness-level exception.
    /// </summary>
    internal static string DecodeSource(ReadOnlySpan<byte> bytes)
        => Encoding.UTF8.GetString(bytes);
}
