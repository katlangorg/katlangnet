using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Deterministic replay driver. Given file and/or directory paths, parses each file
/// once through <c>Parser.ParseSyntax</c> with the fuzzing invariants enabled and no
/// fuzzing loop. This is the reproducer used during triage ("reproduce it without the
/// active fuzzing loop") and a cross-platform smoke test of the harness and corpus.
///
/// Exit code 0 means every input parsed without an unexpected exception or invariant
/// violation; ordinary parser diagnostics are NOT failures. A non-zero exit code
/// reports how many inputs failed, naming each one.
/// </summary>
internal static class Replay
{
    public static int Run(string[] paths)
    {
        var files = new List<string>();
        foreach (var path in paths)
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
            try
            {
                bytes = File.ReadAllBytes(file);
            }
            catch (Exception ex)
            {
                Console.Error.WriteLine($"warning: could not read {file}: {ex.Message}");
                continue;
            }

            var source = Program.DecodeSource(bytes);
            try
            {
                var result = Parser.ParseSyntax(source);
                FuzzInvariants.Check(source, result);
            }
            catch (Exception ex)
            {
                failures++;
                Console.Error.WriteLine($"FAIL {file}");
                Console.Error.WriteLine($"     {ex.GetType().Name}: {ex.Message}");
            }
        }

        Console.WriteLine($"replay: {files.Count} input(s), {failures} failure(s).");
        return failures == 0 ? 0 : 1;
    }
}
