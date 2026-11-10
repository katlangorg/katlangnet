using System.Collections.Immutable;
using System.Diagnostics;
using System.Globalization;
using System.Text;
using System.Text.Json;

namespace KatLang.ParserFuzz;

/// <summary>Why a campaign stopped.</summary>
internal enum SemanticCampaignStop
{
    /// <summary>Every planned case ran.</summary>
    Completed,

    /// <summary>The case budget (<c>--max-cases</c>) was reached before the plan was covered.</summary>
    CaseBudget,

    /// <summary>The time budget (<c>--max-seconds</c>) was reached before the plan was covered.</summary>
    TimeBudget,
}

/// <summary>
/// Bounds, output and the (internal, test-only) execution seams of one <c>semantic-campaign</c>.
/// </summary>
internal sealed record SemanticCampaignOptions
{
    internal const int DefaultCasesPerSeed = 16;
    internal const int DefaultMaxCases = 64;
    internal const int DefaultMaxSeconds = 600;
    internal const int DefaultMaxAttempts = 100;
    internal const int MaxSeedRange = 65_536;
    internal const int MaxCasesPerSeed = 1_000_000;

    public required ulong FirstSeed { get; init; }

    public required ulong LastSeed { get; init; }

    public int CasesPerSeed { get; init; } = DefaultCasesPerSeed;

    /// <summary>The case budget: at most this many cases are EXECUTED (reduction candidates are not counted).</summary>
    public int MaxCases { get; init; } = DefaultMaxCases;

    /// <summary>The time budget, checked before every case and throughout reduction.</summary>
    public TimeSpan MaxTime { get; init; } = TimeSpan.FromSeconds(DefaultMaxSeconds);

    /// <summary>The supervisor's per-execution deadline (cases and reduction candidates).</summary>
    public TimeSpan Deadline { get; init; } = SemanticSupervisor.DefaultDeadline;

    public bool Reduce { get; init; } = true;

    /// <summary>The reducer's execution bound per failure (<see cref="SemanticReductionOptions.MaxAttempts"/>).</summary>
    public int MaxAttempts { get; init; } = DefaultMaxAttempts;

    public required string OutputDirectory { get; init; }

    /// <summary>
    /// Test seam: judge cases and reduction candidates IN PROCESS with this runner instead of
    /// supervised children. <c>semantic-campaign</c> never sets it.
    /// </summary>
    public Func<SemanticCase, SemanticCaseResult>? InProcessRunner { get; init; }

    /// <summary>
    /// Test seam over the child launch (descriptor, result path, mode); default
    /// <see cref="SemanticSupervisor.SelfWorker"/>. The supervisor itself is unchanged.
    /// </summary>
    public Func<string, string, SemanticReplay.Mode, SemanticWorkerCommand>? WorkerCommand { get; init; }

    /// <summary>Test seam: the campaign clock (elapsed time since start); default a stopwatch.</summary>
    public Func<TimeSpan>? Clock { get; init; }

    public bool Supervised => InProcessRunner is null;

    public long PlannedCases => checked((long)(LastSeed - FirstSeed + 1) * CasesPerSeed);

    /// <summary>The bounds a campaign refuses to start without (null when valid).</summary>
    public string? Problem()
    {
        if (LastSeed < FirstSeed) return "the seed range is empty (LAST < FIRST)";
        if (LastSeed - FirstSeed >= MaxSeedRange) return $"the seed range exceeds {MaxSeedRange.ToString(CultureInfo.InvariantCulture)} seeds";
        if (CasesPerSeed is < 1 or > MaxCasesPerSeed) return $"--cases-per-seed must be 1..{MaxCasesPerSeed.ToString(CultureInfo.InvariantCulture)}";
        if (MaxCases < 1) return "--max-cases must be at least 1";
        if (MaxTime <= TimeSpan.Zero) return "--max-seconds must be at least 1";
        if (Deadline <= TimeSpan.Zero || Deadline.TotalMilliseconds > uint.MaxValue - 1)
            return "--deadline-seconds must be 1..4294967 (the supervisor timer range)";
        if (MaxAttempts < 0) return "--max-attempts must be non-negative";
        if (string.IsNullOrWhiteSpace(OutputDirectory)) return "--out must name a directory";
        return null;
    }
}

/// <summary>One failing case of a campaign and what became of its reduction.</summary>
internal sealed record SemanticCampaignFailure(
    string CaseId,
    SemanticVerdict Verdict,
    SemanticFailureSignature Signature,
    string Descriptor,
    string SignatureFile,
    string? ReductionStatus,
    string? ReducedCaseId,
    string? ReducedDescriptor,
    string? ReductionRecord,
    SemanticCaseSize? OriginalSize,
    SemanticCaseSize? ReducedSize,
    int ReductionAttempts,
    int GenerationFailures,
    string? ReductionSkipped)
{
    public string? ReductionStopped { get; init; }
}

/// <summary>The outcome of one campaign: what was planned, what was covered, and every failure.</summary>
internal sealed record SemanticCampaignResult(
    SemanticCampaignOptions Options,
    long Planned,
    int Executed,
    int Passed,
    SemanticCampaignStop Stop,
    string? FirstUncovered,
    string? LastCovered,
    ImmutableSortedDictionary<SemanticVerdict, int> Verdicts,
    ImmutableArray<SemanticCampaignFailure> Failures,
    TimeSpan Elapsed)
{
    public string Describe()
    {
        var uncovered = FirstUncovered is null ? "" : " first-uncovered=" + FirstUncovered;
        return string.Create(CultureInfo.InvariantCulture,
            $"semantic-campaign: seeds {Options.FirstSeed:X}..{Options.LastSeed:X} x {Options.CasesPerSeed}: planned={Planned} executed={Executed} passed={Passed} failed={Failures.Length} stop={SemanticCampaign.StopName(Stop)}{uncovered} elapsed={Elapsed.TotalSeconds:F1}s");
    }
}

/// <summary>
/// <c>semantic-campaign</c> (SEM-2C, fuzz/README.md § Campaigns): a BOUNDED, deterministic search for
/// failing generated cases. It enumerates the seeded recipe ids <c>sem2b/v1/seed/&lt;seed&gt;/&lt;index&gt;</c>
/// for every seed of an inclusive hex range and every index below the cases-per-seed count, in that
/// order, runs each under <see cref="SemanticSupervisor"/> (recipe mode, one child at a time, the
/// descriptor persisted before dispatch), persists every failure with its signature, and — unless
/// <c>--no-reduce</c> — reduces it with <see cref="SemanticReducer"/> (supervised, exact-source
/// candidates) and writes the reduced artifacts. It stops at the first exhausted budget and reports
/// what it covered. It writes only inside its own output directory, which must be new or empty.
/// </summary>
internal static class SemanticCampaign
{
    internal const string SummaryFormat = "kl-sem2c-campaign";
    internal const int SummaryFormatVersion = 1;
    internal const string SummaryFile = "campaign.json";

    private static readonly JsonWriterOptions WriterOptions = new()
    {
        Indented = true,
        NewLine = "\n",
        Encoder = System.Text.Encodings.Web.JavaScriptEncoder.UnsafeRelaxedJsonEscaping,
    };

    internal static string StopName(SemanticCampaignStop stop) => stop switch
    {
        SemanticCampaignStop.Completed => "completed",
        SemanticCampaignStop.CaseBudget => "case-budget",
        SemanticCampaignStop.TimeBudget => "time-budget",
        _ => throw new ArgumentOutOfRangeException(nameof(stop)),
    };

    /// <summary>The planned case ids in campaign order (seed ascending, then index ascending).</summary>
    internal static IEnumerable<(ulong Seed, int Index)> Plan(SemanticCampaignOptions options)
    {
        for (var seed = options.FirstSeed; ; seed++)
        {
            for (var index = 0; index < options.CasesPerSeed; index++) yield return (seed, index);
            if (seed == options.LastSeed) yield break;
        }
    }

    internal static string CaseId(ulong seed, int index) => SemanticCorpus.SeededBuilder(seed, index).CaseId;

    /// <summary>Runs one campaign. The output directory must not exist or must be empty.</summary>
    internal static SemanticCampaignResult Run(SemanticCampaignOptions options, TextWriter log)
    {
        ArgumentNullException.ThrowIfNull(options);
        ArgumentNullException.ThrowIfNull(log);
        if (options.Problem() is { } problem) throw new ArgumentException(problem, nameof(options));
        if (!IsFreshDirectory(options.OutputDirectory))
            throw new IOException($"refusing to write into the non-empty directory '{options.OutputDirectory}'");
        if (ContainsTrackedPaths(options.OutputDirectory))
            throw new IOException($"refusing to write into '{options.OutputDirectory}': it contains Git-tracked paths, including any absent from disk");

        var stopwatch = Stopwatch.StartNew();
        var clock = options.Clock ?? (() => stopwatch.Elapsed);
        var outDir = Directory.CreateDirectory(options.OutputDirectory).FullName;
        var workDir = Path.Combine(outDir, "work");
        var failuresDir = Path.Combine(outDir, "failures");
        var reducedDir = Path.Combine(outDir, "reduced");

        var executed = 0;
        var passed = 0;
        var verdicts = new SortedDictionary<SemanticVerdict, int>();
        var failures = new List<SemanticCampaignFailure>();
        var stop = SemanticCampaignStop.Completed;
        string? firstUncovered = null;
        string? lastCovered = null;
        var timeExhausted = false;

        foreach (var (seed, index) in Plan(options))
        {
            var builder = SemanticCorpus.SeededBuilder(seed, index);
            if (timeExhausted || clock() >= options.MaxTime)
            {
                stop = SemanticCampaignStop.TimeBudget;
                firstUncovered = builder.CaseId;
                break;
            }

            if (executed >= options.MaxCases)
            {
                stop = SemanticCampaignStop.CaseBudget;
                firstUncovered = builder.CaseId;
                break;
            }

            var semanticCase = builder.Build();
            var result = options.InProcessRunner is { } runner ? runner(semanticCase) : Supervise(semanticCase, workDir, options);
            executed++;
            lastCovered = semanticCase.CaseId;
            verdicts[result.Verdict] = verdicts.GetValueOrDefault(result.Verdict) + 1;
            if (result.Passed)
            {
                passed++;
                continue;
            }

            // Persist the failure (descriptor with its result, and its signature) before reducing it.
            var signature = SemanticFailureSignature.Of(result);
            Directory.CreateDirectory(failuresDir);
            var safe = SemanticReplay.SafeName(semanticCase.CaseId);
            var descriptor = Path.Combine(failuresDir, safe + ".json");
            var signatureFile = Path.Combine(failuresDir, safe + ".signature.json");
            File.WriteAllText(descriptor, SemanticDescriptor.Write(semanticCase, result));
            File.WriteAllText(signatureFile, WriteSignature(semanticCase.CaseId, signature, result));
            log.WriteLine($"FAILURE {semanticCase.CaseId}: [{signature}] {(result.Findings.IsEmpty ? "-" : result.Findings[0])}");
            log.WriteLine($"  descriptor={descriptor}");

            var failure = new SemanticCampaignFailure(semanticCase.CaseId, result.Verdict, signature, Relative(outDir, descriptor),
                Relative(outDir, signatureFile), null, null, null, null, null, null, 0, 0, options.Reduce ? null : "disabled (--no-reduce)");
            if (options.Reduce)
            {
                if (clock() >= options.MaxTime)
                {
                    timeExhausted = true;
                    failure = failure with { ReductionSkipped = "time budget exhausted" };
                }
                else
                {
                    failure = Reduce(builder, failure, Path.Combine(reducedDir, safe), outDir, options, clock, log);
                }
            }

            failures.Add(failure);
        }

        var outcome = new SemanticCampaignResult(options, options.PlannedCases, executed, passed, stop, firstUncovered, lastCovered,
            verdicts.ToImmutableSortedDictionary(), [.. failures], clock());
        File.WriteAllText(Path.Combine(outDir, SummaryFile), WriteSummary(outcome));
        if (Directory.Exists(workDir) && !Directory.EnumerateFileSystemEntries(workDir).Any()) Directory.Delete(workDir);
        return outcome;
    }

    /// <summary>One case in a bounded child (recipe mode); passing evidence is removed, failing evidence retained.</summary>
    private static SemanticCaseResult Supervise(SemanticCase semanticCase, string workDir, SemanticCampaignOptions options)
    {
        Directory.CreateDirectory(workDir);
        // Persist the reproducer BEFORE dispatching a child that might crash or hang.
        var descriptor = Path.Combine(workDir, SemanticReplay.SafeName(semanticCase.CaseId) + ".json");
        File.WriteAllText(descriptor, SemanticDescriptor.Write(semanticCase));
        var resultPath = descriptor + ".result.json";
        var command = options.WorkerCommand ?? SemanticSupervisor.SelfWorker;
        var run = SemanticSupervisor.Run(command(descriptor, resultPath, SemanticReplay.Mode.Recipe), options.Deadline);
        var result = run.Result is { } summary && summary.Verdict == run.Verdict
            ? summary.CoverageResult
            // Supervisor failures have no semantic finding location. Keep the same signature as
            // SemanticReduction.SuperviseOne; the detail remains in the retained supervision file.
            : new SemanticCaseResult(semanticCase.CaseId, run.Verdict, [], [], SemanticPath.None, [], []);
        if (result.Passed)
        {
            foreach (var path in new[] { descriptor, resultPath, resultPath + ".supervision.txt", resultPath + ".ready" })
                TryDelete(path);
        }

        return result;
    }

    private static SemanticCampaignFailure Reduce(
        SemanticCaseBuilder builder, SemanticCampaignFailure failure, string reducedDir, string outDir, SemanticCampaignOptions options,
        Func<TimeSpan> clock, TextWriter log)
    {
        var reduction = new SemanticReductionOptions
        {
            MaxAttempts = options.MaxAttempts,
            Supervised = options.Supervised,
            RequiredSignature = failure.Signature,
            ShouldStop = () => clock() >= options.MaxTime,
        };
        if (options.InProcessRunner is { } runner)
        {
            reduction = reduction with { Runner = runner };
        }
        else
        {
            var evidence = Path.Combine(reducedDir, "evidence");
            Directory.CreateDirectory(evidence);
            var counter = 0;
            Func<string, string, SemanticWorkerCommand> command = options.WorkerCommand is { } custom
                ? (d, r) => custom(d, r, SemanticReplay.Mode.ExactSource)
                : SemanticReduction.DefaultWorker;
            reduction = reduction with { Runner = c => SemanticReduction.SuperviseOne(c, evidence, ++counter, command, options.Deadline) };
        }

        var result = SemanticReducer.Reduce(builder, reduction);
        log.WriteLine("  reduce: " + result.Describe());
        if (result.Status == SemanticReductionStatus.NothingToReduce)
        {
            // A passing rerun or a different signature cannot reduce the recorded failure.
            return failure with
            {
                ReductionStatus = result.Status.ToString(),
                ReductionSkipped = "the failure did not reproduce in the reducer's run (observed " + result.Signature + ")",
                ReductionAttempts = result.Attempts,
            };
        }

        var (stem, reduced) = SemanticReduction.WriteArtifacts(result, reducedDir);
        foreach (var generationFailure in result.GenerationFailures.Take(4))
            log.WriteLine($"  GENERATION FAILURE: {generationFailure.Error} choices=[{string.Join(",", generationFailure.Choices)}]");
        log.WriteLine($"  reduced={stem}.json ({reduced.Source.Length.ToString(CultureInfo.InvariantCulture)} source characters)");
        return failure with
        {
            ReductionStatus = result.Status.ToString(),
            ReducedCaseId = reduced.CaseId,
            ReducedDescriptor = Relative(outDir, stem + ".json"),
            ReductionRecord = Relative(outDir, stem + ".reduction.json"),
            OriginalSize = result.OriginalSize,
            ReducedSize = result.ReducedSize,
            ReductionAttempts = result.Attempts,
            GenerationFailures = result.GenerationFailures.Length,
            ReductionStopped = result.Stopped ? "time budget exhausted" : null,
        };
    }

    // ── Summary ─────────────────────────────────────────────────────────────

    /// <summary>
    /// The <c>kl-sem2c-campaign</c> v1 summary. It names the plan, the bounds, what was covered and every
    /// failure with its artifacts (paths relative to the output directory, <c>/</c>-separated). It carries
    /// no clock reading and no absolute path, so a campaign stopped by its case budget (or completed)
    /// writes the same bytes on every run.
    /// </summary>
    internal static string WriteSummary(SemanticCampaignResult result)
    {
        var o = result.Options;
        using var stream = new MemoryStream();
        using (var w = new Utf8JsonWriter(stream, WriterOptions))
        {
            w.WriteStartObject();
            w.WriteString("format", SummaryFormat);
            w.WriteNumber("formatVersion", SummaryFormatVersion);
            w.WriteString("generator", SemanticRecipe.GeneratorId);
            w.WriteNumber("recipeVersion", SemanticRecipe.RecipeVersion);
            w.WriteString("firstSeed", o.FirstSeed.ToString("X", CultureInfo.InvariantCulture));
            w.WriteString("lastSeed", o.LastSeed.ToString("X", CultureInfo.InvariantCulture));
            w.WriteNumber("casesPerSeed", o.CasesPerSeed);
            w.WriteNumber("maxCases", o.MaxCases);
            w.WriteNumber("maxSeconds", (long)Math.Ceiling(o.MaxTime.TotalSeconds));
            w.WriteNumber("deadlineSeconds", (long)Math.Ceiling(o.Deadline.TotalSeconds));
            w.WriteBoolean("reduce", o.Reduce);
            w.WriteNumber("maxAttempts", o.MaxAttempts);
            w.WriteBoolean("supervised", o.Supervised);
            w.WriteNumber("planned", result.Planned);
            w.WriteNumber("executed", result.Executed);
            w.WriteNumber("passed", result.Passed);
            w.WriteNumber("failed", result.Failures.Length);
            w.WriteString("stop", StopName(result.Stop));
            WriteNullable(w, "lastCovered", result.LastCovered);
            WriteNullable(w, "firstUncovered", result.FirstUncovered);
            w.WriteStartObject("verdicts");
            foreach (var (verdict, count) in result.Verdicts) w.WriteNumber(verdict.ToString(), count);
            w.WriteEndObject();
            w.WriteStartArray("failures");
            foreach (var f in result.Failures)
            {
                w.WriteStartObject();
                w.WriteString("caseId", f.CaseId);
                w.WriteString("verdict", f.Verdict.ToString());
                WriteSignatureObject(w, f.Signature);
                w.WriteString("descriptor", f.Descriptor);
                w.WriteString("signatureFile", f.SignatureFile);
                w.WriteStartObject("reduction");
                WriteNullable(w, "status", f.ReductionStatus);
                WriteNullable(w, "skipped", f.ReductionSkipped);
                WriteNullable(w, "stopped", f.ReductionStopped);
                WriteNullable(w, "reducedCaseId", f.ReducedCaseId);
                WriteNullable(w, "descriptor", f.ReducedDescriptor);
                WriteNullable(w, "record", f.ReductionRecord);
                if (f.OriginalSize is { } before) w.WriteNumber("originalSourceLength", before.SourceLength);
                if (f.ReducedSize is { } after) w.WriteNumber("reducedSourceLength", after.SourceLength);
                w.WriteNumber("attempts", f.ReductionAttempts);
                w.WriteNumber("generationFailures", f.GenerationFailures);
                w.WriteEndObject();
                w.WriteEndObject();
            }

            w.WriteEndArray();
            w.WriteEndObject();
        }

        return Encoding.UTF8.GetString(stream.ToArray()) + "\n";
    }

    /// <summary>The per-failure signature sidecar: the case id, the signature and the first finding.</summary>
    internal static string WriteSignature(string caseId, SemanticFailureSignature signature, SemanticCaseResult result)
    {
        using var stream = new MemoryStream();
        using (var w = new Utf8JsonWriter(stream, WriterOptions))
        {
            w.WriteStartObject();
            w.WriteString("format", SummaryFormat + "-signature");
            w.WriteNumber("formatVersion", SummaryFormatVersion);
            w.WriteString("caseId", caseId);
            WriteSignatureObject(w, signature);
            WriteNullable(w, "firstFinding", result.Findings.IsDefaultOrEmpty ? null : result.Findings[0]);
            w.WriteEndObject();
        }

        return Encoding.UTF8.GetString(stream.ToArray()) + "\n";
    }

    private static void WriteSignatureObject(Utf8JsonWriter w, SemanticFailureSignature signature)
    {
        w.WriteStartObject("signature");
        w.WriteString("verdict", signature.Verdict.ToString());
        w.WriteString("member", signature.Member);
        w.WriteString("profile", signature.Profile);
        w.WriteString("facet", signature.Facet);
        w.WriteEndObject();
    }

    private static void WriteNullable(Utf8JsonWriter w, string name, string? value)
    {
        if (value is null) w.WriteNull(name);
        else w.WriteString(name, value);
    }

    private static string Relative(string root, string path) => Path.GetRelativePath(root, path).Replace('\\', '/');

    private static bool IsFreshDirectory(string path)
        => !File.Exists(path) && (!Directory.Exists(path) || !Directory.EnumerateFileSystemEntries(path).Any());

    /// <summary>A fresh directory can still contain tracked files deleted from disk. Check the index before writing.</summary>
    internal static bool ContainsTrackedPaths(string path)
    {
        var fullPath = Path.GetFullPath(path);
        for (var dir = new DirectoryInfo(fullPath); dir is not null; dir = dir.Parent)
        {
            if (!Directory.Exists(Path.Combine(dir.FullName, ".git")) && !File.Exists(Path.Combine(dir.FullName, ".git"))) continue;
            var info = new ProcessStartInfo("git")
            {
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                UseShellExecute = false,
                CreateNoWindow = true,
            };
            foreach (var arg in new[] { "--no-optional-locks", "-C", dir.FullName, "ls-files", "--cached", "-z", "--",
                         ":(literal)" + Path.GetRelativePath(dir.FullName, fullPath).Replace('\\', '/') })
                info.ArgumentList.Add(arg);
            using var process = new Process { StartInfo = info };
            try
            {
                process.Start();
            }
            catch (System.ComponentModel.Win32Exception exception)
            {
                throw new IOException("cannot check the output directory for tracked files (Git could not start)", exception);
            }

            var output = process.StandardOutput.ReadToEndAsync();
            var error = process.StandardError.ReadToEndAsync();
            process.WaitForExit();
            var errorText = error.GetAwaiter().GetResult();
            if (process.ExitCode != 0) throw new IOException("cannot check the output directory for tracked files: " + errorText);
            return output.GetAwaiter().GetResult().Length > 0;
        }

        return false; // Outside a checkout there is no index to overwrite.
    }

    private static void TryDelete(string path)
    {
        try { File.Delete(path); }
        catch (IOException) { /* best effort; evidence of a passing case is not needed */ }
        catch (UnauthorizedAccessException) { /* ditto */ }
    }

    // ── Command ─────────────────────────────────────────────────────────────

    internal const string Usage =
        "usage: semantic-campaign --seeds FIRST[..LAST] [--cases-per-seed N] [--max-cases N] [--max-seconds N] " +
        "[--deadline-seconds N] [--max-attempts N] [--no-reduce] [--out DIR]";

    /// <summary>
    /// <c>semantic-campaign</c>. Exit codes: 0 — every executed case passed (the summary says whether
    /// the plan was covered or a budget stopped it); 1 — at least one failure (persisted, and reduced
    /// unless <c>--no-reduce</c>), or a reduction observed a generator precondition failure; 2 — usage,
    /// a refused output directory, or no case executed.
    /// </summary>
    public static int RunCampaign(string[] args) => RunCampaign(args, Console.Out, seams: null);

    /// <summary><c>semantic-campaign</c> with its internal, test-only seams applied to the parsed options.</summary>
    internal static int RunCampaign(string[] args, TextWriter log, Func<SemanticCampaignOptions, SemanticCampaignOptions>? seams)
    {
        if (!TryParse(args, out var options, out var problem))
        {
            Console.Error.WriteLine("semantic-campaign: " + problem);
            Console.Error.WriteLine(Usage);
            return 2;
        }

        if (seams is not null) options = seams(options);
        if (options.Problem() is { } invalid)
        {
            Console.Error.WriteLine("semantic-campaign: " + invalid);
            return 2;
        }

        SemanticCampaignResult result;
        try
        {
            log.WriteLine($"semantic-campaign: writing to {Path.GetFullPath(options.OutputDirectory)}");
            result = Run(options, log);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException or ArgumentException or NotSupportedException)
        {
            Console.Error.WriteLine("semantic-campaign: " + exception.Message);
            return 2;
        }
        log.WriteLine(result.Describe());
        log.WriteLine("  verdicts: " + (result.Verdicts.IsEmpty ? "-" : string.Join(", ", result.Verdicts.Select(p => $"{p.Key}={p.Value.ToString(CultureInfo.InvariantCulture)}"))));
        if (result.LastCovered is { } last) log.WriteLine("  last covered: " + last);
        log.WriteLine("  summary: " + Path.Combine(Path.GetFullPath(options.OutputDirectory), SummaryFile));
        if (result.Executed == 0)
        {
            Console.Error.WriteLine("semantic-campaign: no case was executed; nothing was verified.");
            return 2;
        }

        return result.Failures.IsEmpty ? 0 : 1;
    }

    internal static bool TryParse(string[] args, out SemanticCampaignOptions options, out string problem)
    {
        options = null!;
        ulong? first = null;
        ulong? last = null;
        var casesPerSeed = SemanticCampaignOptions.DefaultCasesPerSeed;
        var maxCases = SemanticCampaignOptions.DefaultMaxCases;
        var maxSeconds = SemanticCampaignOptions.DefaultMaxSeconds;
        var deadlineSeconds = (int)SemanticSupervisor.DefaultDeadline.TotalSeconds;
        var maxAttempts = SemanticCampaignOptions.DefaultMaxAttempts;
        var reduce = true;
        string? outDir = null;
        for (var i = 1; i < args.Length; i++)
        {
            var arg = args[i];
            if (arg == "--no-reduce")
            {
                reduce = false;
                continue;
            }

            if (i + 1 >= args.Length)
            {
                problem = $"unknown or incomplete argument '{arg}'";
                return false;
            }

            var value = args[++i];
            switch (arg)
            {
                case "--seeds":
                    var parts = value.Split("..", 2);
                    if (!TryHex(parts[0], out var a))
                    {
                        problem = $"--seeds '{value}' is not FIRST[..LAST] in hexadecimal";
                        return false;
                    }

                    var b = a;
                    if (parts.Length == 2 && !TryHex(parts[1], out b))
                    {
                        problem = $"--seeds '{value}' is not FIRST[..LAST] in hexadecimal";
                        return false;
                    }

                    (first, last) = (a, b);
                    break;
                case "--cases-per-seed" when TryCount(value, out casesPerSeed):
                case "--max-cases" when TryCount(value, out maxCases):
                case "--max-seconds" when TryCount(value, out maxSeconds):
                case "--deadline-seconds" when TryCount(value, out deadlineSeconds):
                case "--max-attempts" when TryCount(value, out maxAttempts):
                    break;
                case "--out":
                    outDir = value;
                    break;
                default:
                    problem = $"unknown or invalid argument '{arg} {value}'";
                    return false;
            }
        }

        if (first is null || last is null)
        {
            problem = "--seeds is required";
            return false;
        }

        options = new SemanticCampaignOptions
        {
            FirstSeed = first.Value,
            LastSeed = last.Value,
            CasesPerSeed = casesPerSeed,
            MaxCases = maxCases,
            MaxTime = TimeSpan.FromSeconds(maxSeconds),
            Deadline = TimeSpan.FromSeconds(deadlineSeconds),
            MaxAttempts = maxAttempts,
            Reduce = reduce,
            OutputDirectory = outDir ?? DefaultOutputDirectory(first.Value, last.Value, casesPerSeed),
        };
        problem = "";
        return true;
    }

    /// <summary>
    /// <c>&lt;repository&gt;/artifacts/semantic-campaign/&lt;FIRST&gt;-&lt;LAST&gt;x&lt;N&gt;-&lt;UTC stamp&gt;</c> (git-ignored)
    /// when the current directory is inside a checkout, otherwise under the temporary directory.
    /// </summary>
    internal static string DefaultOutputDirectory(ulong first, ulong last, int casesPerSeed)
    {
        var name = string.Create(CultureInfo.InvariantCulture,
            $"{first:X}-{last:X}x{casesPerSeed}-{DateTime.UtcNow:yyyyMMdd'T'HHmmss'Z'}");
        for (var dir = new DirectoryInfo(Environment.CurrentDirectory); dir is not null; dir = dir.Parent)
        {
            if (Directory.Exists(Path.Combine(dir.FullName, ".git")) || File.Exists(Path.Combine(dir.FullName, ".git")))
                return Path.Combine(dir.FullName, "artifacts", "semantic-campaign", name);
        }

        return Path.Combine(Path.GetTempPath(), "katlang-semantic-campaign", name);
    }

    private static bool TryHex(string text, out ulong value)
    {
        var digits = text.StartsWith("0x", StringComparison.OrdinalIgnoreCase) ? text[2..] : text;
        return ulong.TryParse(digits, NumberStyles.AllowHexSpecifier, CultureInfo.InvariantCulture, out value) && digits.Length > 0;
    }

    private static bool TryCount(string text, out int value)
        => int.TryParse(text, NumberStyles.None, CultureInfo.InvariantCulture, out value);
}
