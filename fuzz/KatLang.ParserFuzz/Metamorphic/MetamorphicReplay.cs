using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>
/// Deterministic replay for the metamorphic target.
///
/// <code>
/// metamorphic-replay PATHS...             replay every seed in the given manifest files/directories
/// metamorphic-replay --payload HEX ...    replay one or more ad-hoc encoded payloads
/// metamorphic-replay --raw PATHS...       replay files whose CONTENT is the payload — the form
///                                         libFuzzer writes crash and corpus artifacts in
/// metamorphic-seeds OUTDIR [PATHS...]     write each seed's raw payload as a libFuzzer corpus file
/// </code>
///
/// <para>Replay runs the SAME decoder, template, executor, and comparator as the fuzzing loop —
/// there is no second implementation of the semantics — and additionally executes every case
/// twice, so a non-deterministic observation is itself a replay failure.</para>
///
/// <para>Exit code 0 iff every seed parsed, every accepted pair satisfied its declared
/// relations, and every replay was deterministic. A REJECTED case is not a failure: it is
/// counted and reported by reason, because a template precondition that does not hold means
/// the pair was never comparable.</para>
/// </summary>
internal static class MetamorphicReplay
{
    public static int RunReplay(string[] args)
    {
        ArgumentNullException.ThrowIfNull(args);

        if (args.Length < 2)
        {
            Console.Error.WriteLine(
                "usage: metamorphic-replay [--raw] (SEED_MANIFEST | DIRECTORY | --payload HEX)...");
            return 2;
        }

        var problems = new List<string>();
        var seeds = CollectSeeds(args.Skip(1), problems);

        // Replaying nothing must never look like a clean run.
        if (seeds.Count == 0 && problems.Count == 0)
        {
            Console.Error.WriteLine("metamorphic-replay: the given paths contain no seeds; nothing was verified.");
            return 2;
        }

        var generated = 0;
        var accepted = 0;
        var rejected = 0;
        var mismatches = 0;
        var nondeterministic = 0;
        var rejectionReasons = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var mismatchKinds = new SortedDictionary<string, int>(StringComparer.Ordinal);

        foreach (var seed in seeds)
        {
            generated++;
            var report = MetamorphicInvariants.Run(seed.Payload);
            var again = MetamorphicInvariants.Run(seed.Payload);

            var deterministic =
                string.Equals(report.Fingerprint, again.Fingerprint, StringComparison.Ordinal)
                && report.Execution.Left == again.Execution.Left
                && report.Execution.Right == again.Execution.Right;

            if (!deterministic)
            {
                nondeterministic++;
                Console.Error.WriteLine($"NONDETERMINISTIC {seed.Location}");
                Console.Error.WriteLine($"     first:  {report.Fingerprint}");
                Console.Error.WriteLine($"     second: {again.Fingerprint}");
            }

            if (report.Accepted) accepted++;
            else
            {
                rejected++;
                rejectionReasons[report.RejectionReason] = rejectionReasons.GetValueOrDefault(report.RejectionReason) + 1;
            }

            if (report.Mismatch is { } mismatch)
            {
                mismatches++;
                var key = $"{mismatch.Class}/{mismatch.Kind}";
                mismatchKinds[key] = mismatchKinds.GetValueOrDefault(key) + 1;
                Console.Error.WriteLine($"MISMATCH {seed.Location}");
                Console.Error.Write(MetamorphicInvariants.Describe(report, mismatch));
            }

            var status = report.Accepted ? "ACCEPTED" : "rejected:" + report.RejectionReason;
            Console.WriteLine(
                $"{seed.Location,-28} {report.Parameters.ToHex()}  {status,-24} {report.Fingerprint}" +
                (seed.Description.Length == 0 ? "" : "  # " + seed.Description));
        }

        foreach (var problem in problems) Console.Error.WriteLine($"MALFORMED SEED {problem}");

        Console.WriteLine(
            $"metamorphic-replay: {generated.ToString(CultureInfo.InvariantCulture)} seed(s), " +
            $"{accepted.ToString(CultureInfo.InvariantCulture)} accepted, " +
            $"{rejected.ToString(CultureInfo.InvariantCulture)} rejected, " +
            $"{mismatches.ToString(CultureInfo.InvariantCulture)} mismatch(es), " +
            $"{nondeterministic.ToString(CultureInfo.InvariantCulture)} nondeterministic, " +
            $"{problems.Count.ToString(CultureInfo.InvariantCulture)} malformed seed line(s).");

        if (rejectionReasons.Count > 0)
            Console.WriteLine("  rejected by reason: " + Join(rejectionReasons));
        if (mismatchKinds.Count > 0)
            Console.WriteLine("  mismatches by relation: " + Join(mismatchKinds));

        return mismatches == 0 && nondeterministic == 0 && problems.Count == 0 ? 0 : 1;
    }

    /// <summary>
    /// Materializes each tracked seed's raw payload as an individual file, so a libFuzzer
    /// campaign can start from the curated corpus without the repository tracking binary blobs.
    /// </summary>
    public static int RunExportSeeds(string[] args)
    {
        ArgumentNullException.ThrowIfNull(args);

        if (args.Length < 2)
        {
            Console.Error.WriteLine("usage: metamorphic-seeds OUTDIR [SEED_MANIFEST...]");
            return 2;
        }

        var outputDirectory = args[1];
        var problems = new List<string>();
        var seeds = CollectSeeds(args.Skip(2), problems);

        Directory.CreateDirectory(outputDirectory);
        // Export overwrites by name but never deletes: the output directory belongs to the
        // caller. Pre-existing files are reported so a stale export is visible rather than
        // silently seeding a campaign with cases the manifest no longer contains.
        var preExisting = Directory.GetFiles(outputDirectory).Length;
        var written = 0;
        foreach (var seed in seeds)
        {
            // Origin + line keeps the name unique even when several manifests are exported at
            // once; the file CONTENT is the payload, which is all libFuzzer reads.
            var name =
                $"{Path.GetFileNameWithoutExtension(seed.Origin)}-" +
                $"{MetamorphicCase.FamilyIdOf(seed.DeclaredFamily)}-" +
                seed.LineNumber.ToString("D4", CultureInfo.InvariantCulture);
            File.WriteAllBytes(Path.Combine(outputDirectory, name), seed.Payload);
            written++;
        }

        foreach (var problem in problems) Console.Error.WriteLine($"MALFORMED SEED {problem}");
        Console.WriteLine(
            $"metamorphic-seeds: wrote {written.ToString(CultureInfo.InvariantCulture)} seed file(s) to {outputDirectory}.");

        var remaining = Directory.GetFiles(outputDirectory).Length;
        if (remaining > written)
        {
            Console.WriteLine(
                $"  note: the directory already held {preExisting.ToString(CultureInfo.InvariantCulture)} file(s) and now holds " +
                $"{remaining.ToString(CultureInfo.InvariantCulture)}; nothing is deleted, so clear it first for an exact corpus.");
        }

        return problems.Count == 0 ? 0 : 1;
    }

    /// <summary>
    /// Loads seeds from manifest paths, from <c>--payload HEX</c> arguments, or — after
    /// <c>--raw</c> — from files whose CONTENT is the payload, which is the form libFuzzer
    /// writes a crash or corpus artifact in.
    /// </summary>
    private static IReadOnlyList<MetamorphicSeed> CollectSeeds(IEnumerable<string> paths, List<string> problems)
    {
        var seeds = new List<MetamorphicSeed>();
        var pending = new Queue<string>(paths);
        var files = new List<string>();
        var rawBytes = false;

        while (pending.Count > 0)
        {
            var argument = pending.Dequeue();
            if (string.Equals(argument, "--raw", StringComparison.Ordinal))
            {
                rawBytes = true;
                continue;
            }

            if (string.Equals(argument, "--payload", StringComparison.Ordinal))
            {
                if (pending.Count == 0)
                {
                    problems.Add("--payload: missing hex payload argument.");
                    continue;
                }

                var hex = pending.Dequeue();
                if (MetamorphicSeedFile.TryParseHex(hex, out var payload, out var problem))
                {
                    // An ad-hoc payload carries no declared family to cross-check: it simply
                    // declares whatever it decodes to. A manifest seed is the form that pins it.
                    seeds.Add(new MetamorphicSeed(
                        "--payload", seeds.Count + 1, MetamorphicDecoder.Decode(payload).Family, payload, "ad-hoc payload"));
                }
                else problems.Add($"--payload {hex}: {problem}");

                continue;
            }

            if (Directory.Exists(argument))
            {
                files.AddRange(Directory.EnumerateFiles(argument, "*", SearchOption.AllDirectories));
                continue;
            }

            if (File.Exists(argument)) files.Add(argument);
            else problems.Add($"{argument}: path not found.");
        }

        files.Sort(StringComparer.Ordinal);
        foreach (var file in files)
        {
            if (!rawBytes)
            {
                seeds.AddRange(MetamorphicSeedFile.Load(file, problems));
                continue;
            }

            try
            {
                var payload = File.ReadAllBytes(file);
                seeds.Add(new MetamorphicSeed(
                    Path.GetFileName(file), 1, MetamorphicDecoder.Decode(payload).Family, payload, "raw artifact"));
            }
            catch (Exception exception)
            {
                problems.Add($"{file}: could not read raw artifact ({exception.GetType().Name}: {exception.Message}).");
            }
        }

        return seeds;
    }

    private static string Join(SortedDictionary<string, int> counts)
        => string.Join(", ", counts.Select(pair => $"{pair.Key}={pair.Value.ToString(CultureInfo.InvariantCulture)}"));
}
