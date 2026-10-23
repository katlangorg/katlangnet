using System.Globalization;
using System.Text;

namespace KatLang.ParserFuzz;

/// <summary>
/// Direct replay of SEM-2B descriptors through the SAME generator, runner, observer and comparator
/// as ordinary execution — there is no replay-only comparison.
///
/// <code>
/// semantic-export CASE_ID OUT.json [--run]     write a case's descriptor (optionally with its result)
/// semantic-replay [--exact-source] [--supervised] DESCRIPTOR...
/// semantic-corpus [--supervised] [--out DIR] [--only PREFIX] [--deadline-seconds N]
/// semantic-worker DESCRIPTOR RESULT [--exact-source]     (child process of a supervised run)
/// </code>
///
/// <para><b>Modes.</b> The default RECIPE mode rebuilds the case from its generator, recipe version
/// and id, and refuses to run when the rebuilt members or expectation differ from the recorded ones
/// (<see cref="SemanticVerdict.RecipeDrift"/>, reported field by field). <c>--exact-source</c> runs
/// the recorded sources against the recorded expectation instead, and says so: it makes no claim
/// that the old recipe still reconstructs.</para>
///
/// <para><b>Exit codes.</b> 0 — every case passed; 1 — a case failed (mismatch, drift, front end,
/// harness, timeout, crash, malformed output); 2 — usage or descriptor error, or NOTHING was
/// verified (zero selected cases is never a successful campaign).</para>
/// </summary>
internal static class SemanticReplay
{
    internal enum Mode
    {
        Recipe,
        ExactSource,
    }

    /// <summary>The outcome of replaying one descriptor in process.</summary>
    internal sealed record Outcome(string CaseId, SemanticVerdict Verdict, string Report, SemanticCaseResult? Result, string? Problem)
    {
        public bool Passed => Problem is null && Verdict == SemanticVerdict.Passed;
    }

    internal static Outcome Replay(string descriptorText, Mode mode)
    {
        if (!SemanticDescriptor.TryParse(descriptorText, out var parsed, out var problem))
            return new Outcome("?", SemanticVerdict.HarnessFailure, "descriptor rejected: " + problem, null, problem);

        var semanticCase = parsed.Case;
        if (mode == Mode.Recipe)
        {
            if (!SemanticCorpus.TryReconstruct(semanticCase.CaseId, parsed.RecipeVersion, out var rebuilt, out var reconstructProblem))
                return new Outcome(semanticCase.CaseId, SemanticVerdict.RecipeDrift, "recipe cannot rebuild the case: " + reconstructProblem, null, null);
            if (Drift(semanticCase, rebuilt) is { } drift)
                return new Outcome(semanticCase.CaseId, SemanticVerdict.RecipeDrift, "recipe drift: " + drift, null, null);
            semanticCase = rebuilt;
        }

        var result = SemanticRunner.Run(semanticCase);
        var report = new StringBuilder()
            .Append(mode == Mode.Recipe ? "[recipe] " : "[exact-source, recipe not re-verified] ")
            .Append(result.Headline);
        foreach (var finding in result.Findings.Take(8)) report.Append(Environment.NewLine).Append("  ").Append(finding);
        if (parsed.RecordedVerdict is { } recorded && recorded != result.Verdict.ToString())
            report.Append(Environment.NewLine).Append("  note: recorded verdict was ").Append(recorded);
        return new Outcome(semanticCase.CaseId, result.Verdict, report.ToString(), result, null);
    }

    /// <summary>Field-by-field difference between a recorded case and the recipe's rebuild, or <c>null</c>.</summary>
    internal static string? Drift(SemanticCase recorded, SemanticCase rebuilt)
    {
        var differences = new List<string>();
        if (recorded.Tier != rebuilt.Tier || recorded.Seed != rebuilt.Seed || recorded.Index != rebuilt.Index)
            differences.Add("generation identity (tier/seed/index) changed");
        if (!recorded.Families.SequenceEqual(rebuilt.Families) || !recorded.Features.SequenceEqual(rebuilt.Features))
            differences.Add("coverage classification changed");
        if (recorded.Members.Length != rebuilt.Members.Length)
            differences.Add($"member count {recorded.Members.Length} -> {rebuilt.Members.Length}");
        foreach (var (a, b) in recorded.Members.Zip(rebuilt.Members))
        {
            if (a.Role != b.Role) differences.Add($"member role {a.Role} -> {b.Role}");
            else if (a.Fingerprint != b.Fingerprint) differences.Add($"member '{a.Role}' source {a.Fingerprint} -> {b.Fingerprint}");
        }

        var e1 = recorded.Expected;
        var e2 = rebuilt.Expected;
        if (e1.Kind != e2.Kind) differences.Add($"kind {e1.Kind} -> {e2.Kind}");
        if (e1.ValueIdentity != e2.ValueIdentity) differences.Add("expected value identity changed");
        if (e1.EmittedCount != e2.EmittedCount) differences.Add($"expected emitted count {e1.EmittedCount} -> {e2.EmittedCount}");
        if (e1.ErrorCategory != e2.ErrorCategory) differences.Add($"expected error {e1.ErrorCategory} -> {e2.ErrorCategory}");
        if (e1.Diagnostic != e2.Diagnostic || e1.DiagnosticPhase != e2.DiagnosticPhase) differences.Add("expected diagnostic changed");
        if (!e1.Events.SequenceEqual(e2.Events)) differences.Add("expected events changed");
        if (!e1.CancelledEventsPrefix.SequenceEqual(e2.CancelledEventsPrefix)) differences.Add("expected cancellation prefix changed");
        if (recorded.Paths != rebuilt.Paths) differences.Add($"intended paths {recorded.Paths} -> {rebuilt.Paths}");
        if (recorded.MinimumCacheHits != rebuilt.MinimumCacheHits) differences.Add("minimum cache hits changed");
        if (!recorded.Profiles.SequenceEqual(rebuilt.Profiles)) differences.Add("profile selection changed");
        return differences.Count == 0 ? null : string.Join("; ", differences);
    }

    // ── Commands ────────────────────────────────────────────────────────────

    public static int RunExport(string[] args)
    {
        if (args.Length < 3)
        {
            Console.Error.WriteLine("usage: semantic-export CASE_ID OUT.json [--run]");
            return 2;
        }

        if (!SemanticCorpus.TryReconstruct(args[1], SemanticRecipe.RecipeVersion, out var semanticCase, out var problem))
        {
            Console.Error.WriteLine("semantic-export: " + problem);
            return 2;
        }

        var result = args.Contains("--run", StringComparer.Ordinal) ? SemanticRunner.Run(semanticCase) : null;
        File.WriteAllText(args[2], SemanticDescriptor.Write(semanticCase, result));
        Console.WriteLine($"wrote {args[2]} ({semanticCase.CaseId}{(result is null ? "" : ", " + result.Verdict)})");
        return 0;
    }

    public static int RunReplay(string[] args)
    {
        var mode = args.Contains("--exact-source", StringComparer.Ordinal) ? Mode.ExactSource : Mode.Recipe;
        var supervised = args.Contains("--supervised", StringComparer.Ordinal);
        var paths = args.Skip(1).Where(a => !a.StartsWith("--", StringComparison.Ordinal)).ToList();
        var files = paths.SelectMany(p => Directory.Exists(p) ? Directory.GetFiles(p, "*.json").Where(f => !f.EndsWith(".result.json", StringComparison.Ordinal)).Order(StringComparer.Ordinal) : (IEnumerable<string>)[p]).ToList();
        if (files.Count == 0)
        {
            Console.Error.WriteLine("semantic-replay: no descriptors given; nothing was verified.");
            return 2;
        }

        var failed = 0;
        var invalid = 0;
        foreach (var file in files)
        {
            string text;
            try
            {
                text = ReadBounded(file);
            }
            catch (Exception exception) when (exception is IOException or UnauthorizedAccessException or InvalidDataException)
            {
                Console.Error.WriteLine($"{file}: {exception.Message}");
                invalid++;
                continue;
            }

            if (supervised)
            {
                // The worker's result goes to a private temporary file, never beside the descriptor
                // (which may be a checked-in fixture).
                var results = Directory.CreateTempSubdirectory("katlang-sem2b-replay-");
                try
                {
                    var resultPath = Path.Combine(results.FullName, SafeName(Path.GetFileName(file)) + ".result.json");
                    var run = SemanticSupervisor.Run(SemanticSupervisor.SelfWorker(file, resultPath, mode), SemanticSupervisor.DefaultDeadline);
                    Console.WriteLine($"{file}: {run.Describe()}");
                    if (run.Verdict != SemanticVerdict.Passed) failed++;
                }
                finally
                {
                    Console.WriteLine("  worker evidence retained at " + results.FullName);
                }

                continue;
            }

            var outcome = Replay(text, mode);
            Console.WriteLine($"{file}: {outcome.Report}");
            if (outcome.Problem is not null) invalid++;
            else if (!outcome.Passed) failed++;
        }

        Console.WriteLine($"semantic-replay: {files.Count} descriptor(s), {files.Count - failed - invalid} passed, {failed} failed, {invalid} invalid.");
        return invalid > 0 && failed == 0 ? 2 : failed > 0 || invalid > 0 ? 1 : 0;
    }

    public static int RunCorpus(string[] args)
    {
        var supervised = args.Contains("--supervised", StringComparer.Ordinal);
        var only = Option(args, "--only");
        var outDir = Option(args, "--out") ?? Path.Combine(Path.GetTempPath(), "katlang-sem2b-" + Environment.ProcessId.ToString(CultureInfo.InvariantCulture));
        var deadline = Option(args, "--deadline-seconds") is { } seconds
            ? TimeSpan.FromSeconds(int.Parse(seconds, CultureInfo.InvariantCulture))
            : SemanticSupervisor.DefaultDeadline;
        var cases = SemanticCorpus.All().Where(c => only is null || c.CaseId.StartsWith(only, StringComparison.Ordinal)).ToList();
        if (cases.Count == 0)
        {
            Console.Error.WriteLine("semantic-corpus: zero cases selected; nothing was verified.");
            return 2;
        }

        Directory.CreateDirectory(outDir);
        var outcomes = new List<(SemanticCase, SemanticCaseResult)>();
        var verdicts = new SortedDictionary<SemanticVerdict, int>();
        foreach (var semanticCase in cases)
        {
            SemanticVerdict verdict;
            if (supervised)
            {
                // Persist the reproducer BEFORE dispatching a child that might crash or hang.
                var descriptor = Path.Combine(outDir, SafeName(semanticCase.CaseId) + ".json");
                File.WriteAllText(descriptor, SemanticDescriptor.Write(semanticCase));
                var run = SemanticSupervisor.Run(SemanticSupervisor.SelfWorker(descriptor, descriptor + ".result.json", Mode.Recipe), deadline);
                verdict = run.Verdict;
                outcomes.Add((semanticCase, run.Result is { } summary && summary.Verdict == run.Verdict
                    ? summary.CoverageResult
                    : new SemanticCaseResult(semanticCase.CaseId, run.Verdict, [run.Detail], [], SemanticPath.None, [], [])));
                if (verdict != SemanticVerdict.Passed) Console.WriteLine($"{semanticCase.CaseId}: {run.Describe()}  descriptor={descriptor}");
            }
            else
            {
                var result = SemanticRunner.Run(semanticCase);
                outcomes.Add((semanticCase, result));
                verdict = result.Verdict;
                if (!result.Passed)
                {
                    var descriptor = Path.Combine(outDir, SafeName(semanticCase.CaseId) + ".json");
                    File.WriteAllText(descriptor, SemanticDescriptor.Write(semanticCase, result));
                    Console.WriteLine($"{result.Headline}  descriptor={descriptor}");
                }
            }

            verdicts[verdict] = verdicts.GetValueOrDefault(verdict) + 1;
        }

        Console.WriteLine($"semantic-corpus: {cases.Count} case(s): " + string.Join(", ", verdicts.Select(p => $"{p.Key}={p.Value}")));
        var coverage = SemanticCoverage.Of(outcomes);
        Console.Write(coverage.Describe());
        if (only is null)
        {
            var floors = coverage.Floors(SemanticCorpus.RequiredInteractions);
            foreach (var violation in floors) Console.WriteLine("FLOOR VIOLATED: " + violation);
            if (floors.Count > 0) return 1;
        }

        return verdicts.Keys.All(v => v == SemanticVerdict.Passed) ? 0 : 1;
    }

    /// <summary>
    /// The supervised child: replays one descriptor through the ordinary pipeline and writes its
    /// result document atomically. A result is written for every verdict — a mismatch is data, not
    /// a crash; only an unreadable descriptor exits without one.
    /// </summary>
    public static int RunWorker(string[] args)
    {
        if (args.Length < 3)
        {
            Console.Error.WriteLine("usage: semantic-worker DESCRIPTOR RESULT [--exact-source]");
            return 2;
        }

        return Work(args[1], args[2], args.Contains("--exact-source", StringComparer.Ordinal) ? Mode.ExactSource : Mode.Recipe);
    }

    internal static int Work(string descriptorPath, string resultPath, Mode mode)
    {
        var outcome = Replay(ReadBounded(descriptorPath), mode);
        if (outcome.Problem is not null)
        {
            Console.Error.WriteLine("semantic-worker: " + outcome.Report);
            return 2;
        }

        var document = outcome.Result is { } result
            ? SemanticDescriptor.WriteResultDocument(result)
            : SemanticDescriptor.WriteResultDocument(new SemanticCaseResult(
                outcome.CaseId, outcome.Verdict, [outcome.Report], [], SemanticPath.None, [], []));
        var temporary = resultPath + ".partial";
        File.WriteAllText(temporary, document);
        File.Move(temporary, resultPath, overwrite: true);
        Console.WriteLine(outcome.Report);
        return 0;
    }

    internal static string ReadBounded(string path)
    {
        var info = new FileInfo(path);
        if (info.Length > SemanticDescriptor.MaxDescriptorChars * 4L)
            throw new InvalidDataException($"descriptor file exceeds its {SemanticDescriptor.MaxDescriptorChars}-character bound");
        return File.ReadAllText(path);
    }

    private static string? Option(string[] args, string name)
    {
        var at = Array.IndexOf(args, name);
        return at >= 0 && at + 1 < args.Length ? args[at + 1] : null;
    }

    internal static string SafeName(string caseId)
        => new(caseId.Select(c => char.IsAsciiLetterOrDigit(c) || c is '-' or '_' ? c : '_').ToArray());
}
