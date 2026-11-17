using System.Collections.Immutable;
using System.Globalization;
using System.Text;
using System.Text.Json;

namespace KatLang.ParserFuzz;

/// <summary>
/// How a campaign failure relates to the batch it was observed in (fuzz/README.md § Campaigns). A
/// failure observed alone — every seeded or in-process case — is <see cref="Standalone"/>; a failure
/// observed in a supervised batch is rerun alone in a single-case child and classified by that rerun.
/// </summary>
internal static class SemanticFailureClass
{
    /// <summary>Observed alone, or the standalone rerun failed with the same signature.</summary>
    internal const string Standalone = "standalone";

    /// <summary>Failed in its batch child; the standalone rerun PASSED. Its reproducer is the batch prefix.</summary>
    internal const string BatchOnly = "batch-only";

    /// <summary>Failed in its batch child; the standalone rerun failed with ANOTHER signature.</summary>
    internal const string BatchDependent = "batch-dependent";

    internal static readonly ImmutableArray<string> All = [Standalone, BatchOnly, BatchDependent];

    /// <summary>The class of a batch failure with signature <paramref name="inBatch"/> whose standalone rerun gave <paramref name="alone"/>.</summary>
    internal static string Of(SemanticFailureSignature inBatch, SemanticCaseResult alone)
        => alone.Passed ? BatchOnly : SemanticFailureSignature.Of(alone) == inBatch ? Standalone : BatchDependent;
}

/// <summary>
/// The batch a failing member was observed in: the original manifest, every member BEFORE it (in
/// order), and its standalone rerun.
/// </summary>
internal sealed record SemanticBatchContext(string Manifest, ImmutableArray<SemanticCase> Prefix, SemanticCaseResult Standalone);

/// <summary>What <see cref="SemanticSequenceReducer"/> concluded.</summary>
internal enum SemanticSequenceStatus
{
    /// <summary>A shorter prefix still reproduces the failure.</summary>
    Reduced,

    /// <summary>The prefix reproduces, but no shorter one did within the bounds (one-minimal unless stopped).</summary>
    Minimal,

    /// <summary>The complete prefix did not reproduce the failure in a fresh batch child: nothing to reduce.</summary>
    NotReproduced,
}

/// <summary>The outcome of one sequence reduction: the shortest reproducing prefix found and the executions spent.</summary>
internal sealed record SemanticSequenceResult(
    SemanticSequenceStatus Status,
    ImmutableArray<SemanticCase> Original,
    ImmutableArray<SemanticCase> Reduced,
    int Attempts,
    bool AttemptLimitReached,
    bool Stopped)
{
    public string Describe() => string.Create(CultureInfo.InvariantCulture,
        $"{Status} prefix {Original.Length} -> {Reduced.Length} member(s); attempts={Attempts}{(AttemptLimitReached ? " (limit reached)" : "")}{(Stopped ? " (stopped)" : "")}");
}

/// <summary>
/// SEQUENCE reduction of a batch-only failure: the members that preceded the failing one are shrunk,
/// order preserved, while running them and then the failing member in ONE batch child still
/// reproduces the failure (delta debugging, ddmin). It first confirms that the complete prefix
/// reproduces in a fresh child and tries the failing member with no prefix at all; every later test
/// keeps a subsequence of the current prefix. Bounded by an execution count and an enclosing
/// stop signal; for a deterministic child the same input gives the same result.
/// </summary>
internal static class SemanticSequenceReducer
{
    /// <param name="prefix">The members that ran before the failing one, in order.</param>
    /// <param name="reproduces">Runs a candidate prefix and then the failing member in one child: does the failure recur?</param>
    internal static SemanticSequenceResult Reduce(
        IReadOnlyList<SemanticCase> prefix, Func<IReadOnlyList<SemanticCase>, bool> reproduces, int maxAttempts, Func<bool>? shouldStop = null)
    {
        ArgumentNullException.ThrowIfNull(prefix);
        ArgumentNullException.ThrowIfNull(reproduces);
        var original = prefix.ToImmutableArray();
        var attempts = 0;
        var limitReached = false;
        var stopped = false;

        bool Test(IReadOnlyList<SemanticCase> candidate)
        {
            if (limitReached || stopped) return false;
            if (shouldStop?.Invoke() == true)
            {
                stopped = true;
                return false;
            }

            if (attempts >= maxAttempts)
            {
                limitReached = true;
                return false;
            }

            attempts++;
            return reproduces(candidate);
        }

        SemanticSequenceResult Result(SemanticSequenceStatus status, IReadOnlyList<SemanticCase> reduced)
            => new(status, original, [.. reduced], attempts, limitReached, stopped);

        if (!Test(original)) return Result(SemanticSequenceStatus.NotReproduced, original);
        if (original.Length == 0) return Result(SemanticSequenceStatus.Minimal, original);
        if (Test([])) return Result(SemanticSequenceStatus.Reduced, []);

        var current = original.ToList();
        var granularity = 2;
        while (current.Count >= 2 && !limitReached && !stopped)
        {
            var chunks = Split(current, granularity);
            var reducedTo = chunks.FirstOrDefault(chunk => Test(chunk));
            if (reducedTo is not null)
            {
                current = reducedTo;
                granularity = 2;
                continue;
            }

            // With two chunks each complement is the other chunk, already tested.
            var complement = granularity == 2 ? null : Enumerable.Range(0, chunks.Count)
                .Select(i => chunks.Where((_, j) => j != i).SelectMany(static c => c).ToList())
                .FirstOrDefault(candidate => Test(candidate));
            if (complement is not null)
            {
                current = complement;
                granularity = Math.Max(granularity - 1, 2);
                continue;
            }

            if (granularity >= current.Count) break;
            granularity = Math.Min(granularity * 2, current.Count);
        }

        return Result(current.Count < original.Length ? SemanticSequenceStatus.Reduced : SemanticSequenceStatus.Minimal, current);
    }

    /// <summary><paramref name="items"/> in <paramref name="parts"/> contiguous chunks of near-equal length.</summary>
    private static List<List<SemanticCase>> Split(List<SemanticCase> items, int parts)
    {
        var chunks = new List<List<SemanticCase>>();
        var start = 0;
        for (var i = 0; i < parts; i++)
        {
            var end = (int)((long)items.Count * (i + 1) / parts);
            if (end > start) chunks.Add(items.GetRange(start, end - start));
            start = end;
        }

        return chunks;
    }
}

/// <summary>
/// Persisted batch SEQUENCES (fuzz/README.md § Campaigns): a directory of numbered member descriptors
/// with a manifest of paths relative to it, replayable from anywhere by <c>semantic-batch-worker</c> and
/// <c>semantic-batch-replay</c>; one supervised batch child over such a sequence; and the result the
/// campaign records for one member of a batch run.
/// </summary>
internal static class SemanticBatchSequence
{
    internal const string ManifestFile = "manifest.txt";
    internal const string ReproducerFormat = "kl-sem2c-batch-reproducer";
    internal const string SequenceFormat = "kl-sem2c-sequence-reduction";
    internal const int FormatVersion = 1;

    private static readonly JsonWriterOptions WriterOptions = new()
    {
        Indented = true,
        NewLine = "\n",
        Encoder = System.Text.Encodings.Web.JavaScriptEncoder.UnsafeRelaxedJsonEscaping,
    };

    /// <summary>
    /// Writes <paramref name="members"/> to <paramref name="directory"/> as <c>NNNNN-&lt;case&gt;.json</c>
    /// descriptors with a <see cref="ManifestFile"/> of relative lines (and the exact-source directive
    /// for <paramref name="mode"/>); returns the manifest's path.
    /// </summary>
    internal static string Persist(string directory, IReadOnlyList<SemanticCase> members, SemanticReplay.Mode mode)
    {
        Directory.CreateDirectory(directory);
        var lines = new List<(string, string)>();
        for (var i = 0; i < members.Count; i++)
        {
            var name = i.ToString("D5", CultureInfo.InvariantCulture) + "-" + SemanticReplay.SafeName(members[i].CaseId) + ".json";
            File.WriteAllText(Path.Combine(directory, name), SemanticDescriptor.Write(members[i]));
            lines.Add((name, name + ".result.json"));
        }

        var manifest = Path.Combine(directory, ManifestFile);
        SemanticSupervisor.WriteManifest(manifest, lines, mode);
        return manifest;
    }

    /// <summary>
    /// Reads a manifest: its mode and each member's case and absolute descriptor/result paths. Fails
    /// with a reason for a malformed line or an unreadable descriptor.
    /// </summary>
    internal static bool TryLoad(string manifest, out SemanticReplay.Mode mode, out ImmutableArray<SemanticBatchMember> members, out string problem)
    {
        mode = SemanticReplay.Mode.Recipe;
        members = [];
        var directory = Path.GetDirectoryName(Path.GetFullPath(manifest)) ?? "";
        var loaded = ImmutableArray.CreateBuilder<SemanticBatchMember>();
        try
        {
            foreach (var line in File.ReadLines(manifest))
            {
                if (line.Length == 0) continue;
                if (line.StartsWith('#'))
                {
                    if (line == SemanticSupervisor.ExactSourceDirective) mode = SemanticReplay.Mode.ExactSource;
                    continue;
                }

                var parts = line.Split('\t');
                if (parts.Length != 2)
                {
                    problem = $"'{line}' is not 'descriptor TAB result'";
                    return false;
                }

                var descriptor = Path.Combine(directory, parts[0]);
                if (!SemanticDescriptor.TryParse(SemanticReplay.ReadBounded(descriptor), out var parsed, out var reason))
                {
                    problem = $"{descriptor}: {reason}";
                    return false;
                }

                loaded.Add(new SemanticBatchMember(parsed.Case, descriptor, Path.Combine(directory, parts[1])));
            }
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException or InvalidDataException)
        {
            problem = exception.Message;
            return false;
        }

        members = loaded.ToImmutable();
        problem = members.IsEmpty ? "the manifest lists no member" : "";
        return !members.IsEmpty;
    }

    /// <summary>Runs a persisted sequence in ONE supervised batch child (results are written beside its descriptors).</summary>
    internal static SemanticBatchRun Run(string manifest, Func<string, SemanticBatchWorkerCommand> command, TimeSpan deadline)
    {
        if (!TryLoad(manifest, out _, out var members, out var problem))
            throw new InvalidDataException($"cannot run the sequence '{manifest}': {problem}");
        return SemanticSupervisor.RunBatch(command(manifest), members, deadline);
    }

    /// <summary>
    /// Replays a persisted reproducer WITHOUT writing beside it: its members are copied, in order and
    /// in its mode, to a fresh temporary directory that is run and then removed.
    /// </summary>
    internal static SemanticBatchRun Replay(string manifest, Func<string, SemanticBatchWorkerCommand> command, TimeSpan deadline)
    {
        if (!TryLoad(manifest, out var mode, out var members, out var problem))
            throw new InvalidDataException($"cannot replay '{manifest}': {problem}");
        var scratch = Directory.CreateTempSubdirectory("katlang-sem2c-batch-replay-");
        try
        {
            return Run(Persist(scratch.FullName, [.. members.Select(static m => m.Case)], mode), command, deadline);
        }
        finally
        {
            TryDeleteDirectory(scratch.FullName);
        }
    }

    /// <summary>
    /// The result a campaign records for member <paramref name="index"/> of a batch run: its judged
    /// result; the child's own failure when the child died after writing this LAST member's result;
    /// and, for a member without a result, the child's failure (or a missing observation).
    /// </summary>
    internal static SemanticCaseResult MemberResult(SemanticBatchRun run, int index)
    {
        var member = run.Members[index];
        if (member.Verdict is not { } verdict)
            return new SemanticCaseResult(member.Case.CaseId, run.ChildFailure ?? SemanticVerdict.MissingObservation, [], [], SemanticPath.None, [], []);

        // Supervisor-classified failures carry no semantic finding location (as a single supervised run).
        var result = member.Summary is { } summary && summary.Verdict == verdict
            ? summary.CoverageResult
            : new SemanticCaseResult(member.Case.CaseId, verdict, [], [], SemanticPath.None, [], []);
        // A child can also die after writing its last result (including during shutdown).
        if (index == run.Members.Length - 1 && run.ChildFailure is { } failure)
            result = result with { Verdict = failure, Findings = [], FindingRecords = [] };
        return result;
    }

    /// <summary>The LAST member's recorded result when the child reached it (every earlier member has a result), else <c>null</c>.</summary>
    internal static SemanticCaseResult? LastResult(SemanticBatchRun run)
        => run.Members.Take(run.Members.Length - 1).Any(static m => m.Verdict is null) ? null : MemberResult(run, run.Members.Length - 1);

    /// <summary>
    /// The <c>kl-sem2c-batch-reproducer</c> v1 record beside a complete batch reproducer: the failing
    /// case (the manifest's LAST member), its class, its signature in the batch, its standalone rerun, the
    /// original campaign manifest, and every member's id in order.
    /// </summary>
    internal static string WriteReproducerRecord(
        string recipe, string caseId, string classification, SemanticFailureSignature signature, SemanticCaseResult standalone,
        string originalManifest, IReadOnlyList<SemanticCase> members)
    {
        using var stream = new MemoryStream();
        using (var w = new Utf8JsonWriter(stream, WriterOptions))
        {
            w.WriteStartObject();
            w.WriteString("format", ReproducerFormat);
            w.WriteNumber("formatVersion", FormatVersion);
            w.WriteString("generator", SemanticRecipe.GeneratorId);
            w.WriteNumber("recipeVersion", SemanticRecipe.RecipeVersion);
            w.WriteString("recipe", recipe);
            w.WriteString("caseId", caseId);
            w.WriteString("classification", classification);
            WriteSignature(w, "signature", signature);
            w.WriteStartObject("standalone");
            w.WriteString("verdict", standalone.Verdict.ToString());
            WriteSignature(w, "signature", SemanticFailureSignature.Of(standalone));
            w.WriteEndObject();
            w.WriteString("originalManifest", originalManifest);
            w.WriteString("manifest", ManifestFile);
            w.WriteStartArray("members");
            foreach (var member in members) w.WriteStringValue(member.CaseId);
            w.WriteEndArray();
            w.WriteEndObject();
        }

        return Encoding.UTF8.GetString(stream.ToArray()) + "\n";
    }

    /// <summary>The <c>kl-sem2c-sequence-reduction</c> v1 record beside a reduced sequence.</summary>
    internal static string WriteSequenceRecord(string caseId, SemanticFailureSignature signature, SemanticSequenceResult result)
    {
        using var stream = new MemoryStream();
        using (var w = new Utf8JsonWriter(stream, WriterOptions))
        {
            w.WriteStartObject();
            w.WriteString("format", SequenceFormat);
            w.WriteNumber("formatVersion", FormatVersion);
            w.WriteString("generator", SemanticRecipe.GeneratorId);
            w.WriteNumber("recipeVersion", SemanticRecipe.RecipeVersion);
            w.WriteString("caseId", caseId);
            WriteSignature(w, "signature", signature);
            w.WriteString("status", result.Status.ToString());
            w.WriteNumber("attempts", result.Attempts);
            w.WriteBoolean("attemptLimitReached", result.AttemptLimitReached);
            w.WriteBoolean("stopped", result.Stopped);
            w.WriteString("manifest", ManifestFile);
            w.WriteStartArray("originalPrefix");
            foreach (var member in result.Original) w.WriteStringValue(member.CaseId);
            w.WriteEndArray();
            w.WriteStartArray("reducedPrefix");
            foreach (var member in result.Reduced) w.WriteStringValue(member.CaseId);
            w.WriteEndArray();
            w.WriteEndObject();
        }

        return Encoding.UTF8.GetString(stream.ToArray()) + "\n";
    }

    private static void WriteSignature(Utf8JsonWriter w, string name, SemanticFailureSignature signature)
    {
        w.WriteStartObject(name);
        w.WriteString("verdict", signature.Verdict.ToString());
        w.WriteString("member", signature.Member);
        w.WriteString("profile", signature.Profile);
        w.WriteString("facet", signature.Facet);
        w.WriteEndObject();
    }

    internal static void TryDeleteDirectory(string path)
    {
        try
        {
            if (Directory.Exists(path)) Directory.Delete(path, recursive: true);
        }
        catch (IOException) { /* best effort: scratch evidence of a judged candidate is not needed */ }
        catch (UnauthorizedAccessException) { /* ditto */ }
    }

    // ── Command ─────────────────────────────────────────────────────────────

    internal const string ReplayUsage = "usage: semantic-batch-replay MANIFEST [--deadline-seconds N]";

    /// <summary>
    /// <c>semantic-batch-replay MANIFEST</c>: replays a persisted batch reproducer (a campaign's
    /// <c>failures/&lt;case&gt;.batch/manifest.txt</c> or a reduced <c>reduced/&lt;case&gt;.sequence/…</c>
    /// manifest) in ONE supervised batch child, exactly as the campaign ran it, and prints every member's
    /// verdict. Exit codes: 0 — every member passed; 1 — a member failed (the reproducer reproduces when
    /// its LAST member fails); 2 — usage or an unreadable manifest.
    /// </summary>
    public static int RunReplay(string[] args) => RunReplay(args, Console.Out, SemanticSupervisor.SelfBatchWorker);

    internal static int RunReplay(string[] args, TextWriter log, Func<string, SemanticBatchWorkerCommand> command)
    {
        var deadline = SemanticSupervisor.DefaultDeadline;
        var paths = new List<string>();
        for (var i = 1; i < args.Length; i++)
        {
            if (args[i] == "--deadline-seconds" && i + 1 < args.Length
                && int.TryParse(args[i + 1], NumberStyles.None, CultureInfo.InvariantCulture, out var seconds) && seconds > 0)
            {
                deadline = TimeSpan.FromSeconds(seconds);
                i++;
            }
            else if (args[i].StartsWith("--", StringComparison.Ordinal))
            {
                Console.Error.WriteLine(ReplayUsage);
                return 2;
            }
            else
            {
                paths.Add(args[i]);
            }
        }

        if (paths.Count != 1)
        {
            Console.Error.WriteLine(ReplayUsage);
            return 2;
        }

        SemanticBatchRun run;
        try
        {
            run = Replay(paths[0], command, deadline);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException or InvalidDataException)
        {
            Console.Error.WriteLine("semantic-batch-replay: " + exception.Message);
            return 2;
        }

        for (var i = 0; i < run.Members.Length; i++)
        {
            var result = MemberResult(run, i);
            var reached = run.Members[i].Verdict is not null;
            log.WriteLine(string.Create(CultureInfo.InvariantCulture,
                $"{i,5} {run.Members[i].Case.CaseId}: {result.Verdict}{(reached ? "" : " (no result)")}{(result.Findings.IsDefaultOrEmpty ? "" : " " + result.Findings[0])}"));
        }

        var failed = Enumerable.Range(0, run.Members.Length).Count(i => !MemberResult(run, i).Passed);
        log.WriteLine(string.Create(CultureInfo.InvariantCulture,
            $"semantic-batch-replay: {run.Members.Length} member(s), {failed} failed; child {(run.ChildFailure is { } child ? child.ToString() : "exited cleanly")}; last member {MemberResult(run, run.Members.Length - 1).Verdict}"));
        return failed == 0 ? 0 : 1;
    }
}
