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

        // Phase-4 evaluator subcommands.
        if (args.Length > 0 && args[0] == "eval-probe-child")
            return EvaluatorProbe.RunChild(args);      // dangerous evaluation, isolated child
        if (args.Length > 0 && args[0] == "eval-probe")
            return EvaluatorProbe.RunParent(args);     // resource-probe coordinator
        if (args.Length > 0 && args[0] == "evaluator-replay")
            return EvaluatorReplay.RunReplay(args);    // phase-aware evaluator replay
        if (args.Length > 0 && args[0] == "classify")
            return EvaluatorReplay.RunClassify(args);  // eligibility-classifier replay
        if (args.Length > 0 && args[0] == "run")
            return FrontEndStageProbe.RunSources(args);   // evaluate sources (semantic matrix)
        if (args.Length > 0 && args[0] == "stage-probe")
            return FrontEndStageProbe.Run(args);       // per-stage frontend timing

        // Phase-5 operational-metamorphic subcommands.
        if (args.Length > 0 && args[0] == "metamorphic-replay")
            return MetamorphicReplay.RunReplay(args);      // relation-aware seed replay
        if (args.Length > 0 && args[0] == "metamorphic-seeds")
            return MetamorphicReplay.RunExportSeeds(args); // export seed payloads as a corpus

        // Phase-6 UTF-16 lexer/parser/span subcommands.
        if (args.Length > 0 && args[0] == "utf16-replay")
            return Utf16Replay.RunReplay(args);            // exact code-unit replay
        if (args.Length > 0 && args[0] == "utf16-seeds")
            return Utf16Replay.RunExportSeeds(args);       // export seed payloads as a corpus

        // Phase-6 source/module input-size measurement subcommands (no network; no libFuzzer).
        if (args.Length > 0 && args[0] == "source-probe")
            return SourceModuleProbe.RunSource(args);          // deterministic source shapes
        if (args.Length > 0 && args[0] == "source-probe-child")
            return SourceModuleProbe.RunSourceChild(args);     // isolated RSS calibration
        if (args.Length > 0 && args[0] == "module-probe")
            return SourceModuleProbe.RunModule(args);          // module-graph scenarios (fake downloader)
        if (args.Length > 0 && args[0] == "module-depth-search")
            return SourceModuleProbe.RunModuleDepthSearch(args); // isolated deep-chain no-crash validation
        if (args.Length > 0 && args[0] == "module-depth-child")
            return SourceModuleProbe.RunModuleDepthChild(args);  // one isolated deep import chain

        if (args.Length > 0)
            return Replay.Run(args);            // raw-parser replay (Phase 1)

        // libFuzzer mode. The delegate must let every unexpected exception, stack
        // overflow, hang, and invariant violation escape so the fuzzing engine records
        // them as crashes. KATLANG_FUZZ_MODE selects the target: default (unset) is the
        // raw parser — UNCHANGED and never replaced — and "frontend" fuzzes the default
        // elaborated pipeline (FrontEndPipeline.Process, no downloader).
        var mode = Environment.GetEnvironmentVariable("KATLANG_FUZZ_MODE");
        if (string.Equals(mode, "frontend", StringComparison.OrdinalIgnoreCase))
        {
            Fuzzer.LibFuzzer.Run(static bytes => FrontEndInvariants.Check(DecodeSource(bytes)));
        }
        else if (string.Equals(mode, "metamorphic", StringComparison.OrdinalIgnoreCase))
        {
            // Operational-metamorphic target. The bytes are NOT a KatLang program: they are
            // parameters for a trusted template that emits a pair of programs whose
            // equivalence is guaranteed by construction, which the harness then runs with
            // independent state and compares under an explicitly declared relation.
            Fuzzer.LibFuzzer.Run(static bytes => MetamorphicInvariants.Check(bytes));
        }
        else if (string.Equals(mode, "utf16", StringComparison.OrdinalIgnoreCase))
        {
            // UTF-16 lexer/parser/span target. The bytes are NOT source text: they select a trusted
            // template and a named run of UTF-16 code units, so ill-formed UTF-16 — isolated
            // surrogates above all — stays representable, which UTF-8 decoding could never do.
            Fuzzer.LibFuzzer.Run(static bytes => Utf16Invariants.Check(bytes));
        }
        else if (string.Equals(mode, "evaluator", StringComparison.OrdinalIgnoreCase))
        {
            // Terminating evaluator subset only: EvaluatorEligibility excludes programs
            // that may not terminate or may allocate without a practical bound; those are
            // characterized separately by the process-isolated resource probes.
            Fuzzer.LibFuzzer.Run(static bytes => EvaluatorInvariants.Check(DecodeSource(bytes)));
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
