using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Deterministic replay for the evaluator harness.
///
///   evaluator-replay PATHS...  runs every evaluator phase per input, reporting the exact
///                              phase for any failure plus eligible/ineligible totals by
///                              reason so the campaign's scope is explicit.
///   classify PATHS...          reports the eligibility verdict, reasons, AST node count,
///                              and detected call-graph cycles for each input.
/// </summary>
internal static class EvaluatorReplay
{
    public static int RunReplay(string[] args)
    {
        var files = Collect(args);
        int failures = 0, eligible = 0, ineligible = 0, parseErr = 0;
        var reasons = new SortedDictionary<string, int>(StringComparer.Ordinal);

        foreach (var file in files)
        {
            if (!TryRead(file, out var source)) continue;

            // Scope accounting (independent of the invariant run).
            var parse = Parser.Parse(source);
            if (parse.HasErrors) parseErr++;
            else
            {
                var v = EvaluatorEligibility.Classify(source, parse.Root);
                if (v.Eligible) eligible++;
                else
                {
                    ineligible++;
                    foreach (var r in v.Reasons) reasons[r] = reasons.GetValueOrDefault(r) + 1;
                }
            }

            var phase = EvaluatorPhase.FrontendParse;
            try
            {
                EvaluatorInvariants.Run(source, ref phase);
            }
            catch (Exception ex)
            {
                failures++;
                Console.Error.WriteLine($"FAIL [{phase}] {file}");
                Console.Error.WriteLine($"     {ex.GetType().Name}: {ex.Message}");
            }
        }

        Console.WriteLine($"evaluator-replay: {files.Count} input(s), {failures} failure(s).");
        Console.WriteLine($"  scope: eligible={eligible} ineligible={ineligible} frontend-errors={parseErr}");
        if (reasons.Count > 0)
            Console.WriteLine("  ineligible by reason: " + string.Join(", ", reasons.Select(kv => $"{kv.Key}={kv.Value}")));
        return failures == 0 ? 0 : 1;
    }

    public static int RunClassify(string[] args)
    {
        var files = Collect(args);
        int eligible = 0, ineligible = 0, parseErr = 0;
        var reasons = new SortedDictionary<string, int>(StringComparer.Ordinal);

        foreach (var file in files)
        {
            if (!TryRead(file, out var source)) continue;
            var parse = Parser.Parse(source);
            if (parse.HasErrors)
            {
                parseErr++;
                Console.WriteLine($"{Path.GetFileName(file),-34} frontend-errors");
                continue;
            }

            var v = EvaluatorEligibility.Classify(source, parse.Root);
            if (v.Eligible) eligible++; else { ineligible++; foreach (var r in v.Reasons) reasons[r] = reasons.GetValueOrDefault(r) + 1; }
            var cycles = v.Cycles.Count == 0 ? "" : "  cycles=" + string.Join(";", v.Cycles.Take(3));
            Console.WriteLine($"{Path.GetFileName(file),-34} {(v.Eligible ? "ELIGIBLE  " : "ineligible")} nodes={v.NodeCount,-6} {v.ReasonText}{cycles}");
        }

        Console.WriteLine($"totals: eligible={eligible} ineligible={ineligible} frontend-errors={parseErr}");
        if (reasons.Count > 0)
            Console.WriteLine("ineligible by reason: " + string.Join(", ", reasons.Select(kv => $"{kv.Key}={kv.Value}")));
        return 0;
    }

    private static List<string> Collect(string[] args)
    {
        var files = new List<string>();
        foreach (var path in args.Skip(1))
        {
            if (Directory.Exists(path)) files.AddRange(Directory.EnumerateFiles(path, "*", SearchOption.AllDirectories));
            else if (File.Exists(path)) files.Add(path);
            else Console.Error.WriteLine($"warning: path not found, skipping: {path}");
        }
        files.Sort(StringComparer.Ordinal);
        return files;
    }

    private static bool TryRead(string file, out string source)
    {
        source = "";
        try { source = Program.DecodeSource(File.ReadAllBytes(file)); return true; }
        catch (Exception ex) { Console.Error.WriteLine($"warning: could not read {file}: {ex.Message}"); return false; }
    }
}
