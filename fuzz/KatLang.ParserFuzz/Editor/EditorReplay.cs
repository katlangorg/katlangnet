using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>
/// Deterministic replay for the editor target.
///
/// <code>
/// editor-replay PATHS...              replay every seed in the given manifest files/directories
/// editor-replay --payload HEX ...     replay one or more ad-hoc payloads
/// editor-replay --raw PATHS...        replay files whose CONTENT is the payload — the form
///                                     libFuzzer writes crash and corpus artifacts in
/// editor-seeds OUTDIR [PATHS...]      write each seed's raw payload as a libFuzzer corpus file
/// </code>
///
/// <para>Replay runs the SAME decoder, builder, executor and relations as the fuzzing loop, and runs
/// every case TWICE — a non-deterministic observation is itself a replay failure. Exit code 0 iff
/// every case was read, executed without an invariant violation, and replayed identically. Replaying
/// nothing is a failure, not a clean run.</para>
/// </summary>
internal static class EditorReplay
{
    public static int RunReplay(string[] args)
    {
        ArgumentNullException.ThrowIfNull(args);

        if (args.Length < 2)
        {
            Console.Error.WriteLine("usage: editor-replay [--raw] (SEED_MANIFEST | DIRECTORY | --payload HEX)...");
            return 2;
        }

        var problems = new List<string>();
        var seeds = CollectSeeds(args.Skip(1), problems);

        if (seeds.Count == 0 && problems.Count == 0)
        {
            Console.Error.WriteLine("editor-replay: the given paths contain no seeds; nothing was verified.");
            return 2;
        }

        var failures = 0;
        var nondeterministic = 0;
        var templates = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var surfaces = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var outcomes = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var fingerprints = new HashSet<string>(StringComparer.Ordinal);

        foreach (var seed in seeds)
        {
            EditorReport first;
            var phase = EditorPhase.Build;
            try
            {
                first = EditorInvariants.Run(seed.Payload, ref phase);
            }
            catch (Exception exception)
            {
                failures++;
                Console.Error.WriteLine($"FAIL {seed.Location}  [phase={phase}]");
                Console.Error.WriteLine($"     payload: {Hex(seed.Payload)}");
                Console.Error.WriteLine($"     {exception.GetType().Name}: {exception.Message}");
                continue;
            }

            var second = EditorInvariants.Run(seed.Payload);
            if (!string.Equals(first.Fingerprint, second.Fingerprint, StringComparison.Ordinal)
                || !string.Equals(first.Case.HexUnits, second.Case.HexUnits, StringComparison.Ordinal)
                || !string.Equals(first.Case.EditedHexUnits, second.Case.EditedHexUnits, StringComparison.Ordinal))
            {
                nondeterministic++;
                Console.Error.WriteLine($"NONDETERMINISTIC {seed.Location}");
                Console.Error.WriteLine($"     first:  {first.Fingerprint}");
                Console.Error.WriteLine($"     second: {second.Fingerprint}");
            }

            var templateId = EditorTables.TemplateOf(first.Case.Parameters.Template).Id;
            templates[templateId] = templates.GetValueOrDefault(templateId) + 1;
            var surface = first.Case.Parameters.Surface.ToString();
            surfaces[surface] = surfaces.GetValueOrDefault(surface) + 1;
            var outcome = first.Observation.Outcome.ToString();
            outcomes[outcome] = outcomes.GetValueOrDefault(outcome) + 1;
            fingerprints.Add(first.Fingerprint);

            Console.WriteLine($"{seed.Location,-28} {Hex(seed.Payload),-40} units={first.Case.HexUnits}");
            Console.WriteLine($"{"",-28} {first.Fingerprint}");
        }

        foreach (var problem in problems)
        {
            failures++;
            Console.Error.WriteLine($"MALFORMED {problem}");
        }

        Console.WriteLine(
            $"editor-replay: {Num(seeds.Count)} case(s), {Num(failures)} failure(s), " +
            $"{Num(nondeterministic)} nondeterministic, {Num(fingerprints.Count)} distinct fingerprint(s).");
        Report("templates", templates);
        Report("surfaces", surfaces);
        Report("outcomes", outcomes);

        return failures == 0 && nondeterministic == 0 ? 0 : 1;
    }

    /// <summary>Materializes each tracked seed's payload as a libFuzzer corpus file.</summary>
    public static int RunExportSeeds(string[] args)
    {
        ArgumentNullException.ThrowIfNull(args);

        if (args.Length < 2)
        {
            Console.Error.WriteLine("usage: editor-seeds OUTDIR [SEED_MANIFEST | DIRECTORY]...");
            return 2;
        }

        var outDir = args[1];
        var sources = args.Length > 2
            ? args.Skip(2)
            : [Path.Combine(AppContext.BaseDirectory, "EditorTestcases")];

        var problems = new List<string>();
        var seeds = CollectSeeds(sources, problems);

        foreach (var problem in problems) Console.Error.WriteLine($"MALFORMED {problem}");
        if (problems.Count != 0) return 1;

        if (seeds.Count == 0)
        {
            Console.Error.WriteLine("editor-seeds: no seeds found; refusing to write an empty corpus.");
            return 2;
        }

        Directory.CreateDirectory(outDir);
        var existing = Directory.EnumerateFiles(outDir).Count();
        if (existing != 0)
            Console.Error.WriteLine(
                $"warning: {Num(existing)} file(s) already in {outDir}; nothing is deleted here, so clear it first " +
                "for an exact corpus.");

        var index = 0;
        foreach (var seed in seeds)
        {
            var name = $"seed-{index.ToString("D3", CultureInfo.InvariantCulture)}-{EditorTables.TemplateOf(seed.DeclaredTemplate).Id}";
            File.WriteAllBytes(Path.Combine(outDir, name), seed.Payload);
            index++;
        }

        Console.WriteLine($"editor-seeds: wrote {Num(index)} payload(s) to {outDir}");
        return 0;
    }

    private static List<EditorSeed> CollectSeeds(IEnumerable<string> args, List<string> problems)
    {
        var seeds = new List<EditorSeed>();
        var raw = false;
        var pendingPayloads = false;

        foreach (var arg in args)
        {
            if (string.Equals(arg, "--raw", StringComparison.Ordinal)) { raw = true; continue; }
            if (string.Equals(arg, "--payload", StringComparison.Ordinal)) { pendingPayloads = true; continue; }

            if (pendingPayloads)
            {
                if (Utf16SeedFile.TryParseHexBytes(arg, out var payload, out var problem))
                    seeds.Add(new EditorSeed("--payload", seeds.Count + 1, EditorDecoder.Decode(payload).Template, payload, "ad-hoc"));
                else
                    problems.Add($"--payload {arg}: {problem}");
                continue;
            }

            if (Directory.Exists(arg))
            {
                var files = Directory.EnumerateFiles(arg, "*", SearchOption.AllDirectories).ToList();
                files.Sort(StringComparer.Ordinal);
                foreach (var file in files) LoadOne(file, raw, seeds, problems);
            }
            else if (File.Exists(arg))
            {
                LoadOne(arg, raw, seeds, problems);
            }
            else
            {
                problems.Add($"{arg}: path not found.");
            }
        }

        return seeds;
    }

    private static void LoadOne(string file, bool raw, List<EditorSeed> seeds, List<string> problems)
    {
        if (raw)
        {
            byte[] payload;
            try
            {
                payload = File.ReadAllBytes(file);
            }
            catch (Exception exception)
            {
                problems.Add($"{file}: could not read ({exception.GetType().Name}: {exception.Message}).");
                return;
            }

            var template = EditorDecoder.Decode(payload).Template;
            seeds.Add(new EditorSeed(Path.GetFileName(file), 1, template, payload, "raw artifact"));
            return;
        }

        seeds.AddRange(EditorSeedFile.Load(file, problems));
    }

    private static void Report(string title, SortedDictionary<string, int> counts)
    {
        if (counts.Count == 0) return;
        Console.WriteLine($"  {title} ({Num(counts.Count)}):");
        foreach (var (key, value) in counts) Console.WriteLine($"    {key} = {Num(value)}");
    }

    private static string Hex(byte[] payload)
        => string.Join(' ', payload.Select(b => b.ToString("X2", CultureInfo.InvariantCulture)));

    private static string Num(int value) => value.ToString(CultureInfo.InvariantCulture);
}
