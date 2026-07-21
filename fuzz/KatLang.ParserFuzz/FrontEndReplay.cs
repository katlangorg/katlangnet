namespace KatLang.ParserFuzz;

/// <summary>
/// Deterministic, phase-aware replay for the frontend harness. Given files/directories,
/// runs every frontend stage on each input with no fuzzing loop and reports, for any
/// failure, the exact phase that threw (raw parse / raw invariants / frontend process /
/// frontend traversal / diagnostic-prefix / determinism / wrapper parity). Used to triage
/// discovered crashes and to smoke-test the frontend corpus on any platform.
///
/// Exit 0 iff every input passed all stages; ordinary parser/frontend diagnostics are not
/// failures.
/// </summary>
internal static class FrontEndReplay
{
    public static int Run(string[] args)
    {
        // args[0] == "frontend-replay"; the rest are paths.
        var files = new List<string>();
        foreach (var path in args.Skip(1))
        {
            if (Directory.Exists(path))
                files.AddRange(Directory.EnumerateFiles(path, "*", SearchOption.AllDirectories));
            else if (File.Exists(path))
                files.Add(path);
            else
                Console.Error.WriteLine($"warning: path not found, skipping: {path}");
        }

        files.Sort(StringComparer.Ordinal);

        int failures = 0;
        foreach (var file in files)
        {
            byte[] bytes;
            try { bytes = File.ReadAllBytes(file); }
            catch (Exception ex) { Console.Error.WriteLine($"warning: could not read {file}: {ex.Message}"); continue; }

            var source = Program.DecodeSource(bytes);
            var phase = FrontEndPhase.RawParse;
            try
            {
                FrontEndInvariants.Run(source, ref phase);
            }
            catch (Exception ex)
            {
                failures++;
                Console.Error.WriteLine($"FAIL [{phase}] {file}");
                Console.Error.WriteLine($"     {ex.GetType().Name}: {ex.Message}");
            }
        }

        Console.WriteLine($"frontend-replay: {files.Count} input(s), {failures} failure(s).");
        return failures == 0 ? 0 : 1;
    }
}
