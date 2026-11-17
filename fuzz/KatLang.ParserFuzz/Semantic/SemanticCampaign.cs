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

    /// <summary>An exhaustive campaign's default time budget: long enough to complete either finite recipe.</summary>
    internal const int DefaultExhaustiveMaxSeconds = 7_200;

    internal const int DefaultBatchSize = 64;
    internal const int MaxBatchSize = 4_096;

    /// <summary>The first seed of the plan (ignored by an exhaustive campaign).</summary>
    public ulong FirstSeed { get; init; }

    /// <summary>The last seed of the plan, inclusive (ignored by an exhaustive campaign).</summary>
    public ulong LastSeed { get; init; }

    /// <summary>
    /// The seeded recipe searched (<c>--recipe</c>): one of <see cref="SemanticCorpus.SeededRecipes"/>,
    /// the id segment of every planned case. The default is the compositional <c>seed</c> recipe.
    /// </summary>
    public string Recipe { get; init; } = SemanticCorpus.SeedRecipe;

    /// <summary>
    /// <c>--exhaustive</c>: run EVERY program of a finite recipe (<see cref="SemanticCorpus.FiniteRecipes"/>,
    /// enumerated by <see cref="SemanticExhaustive"/>) once, in enumeration order, instead of a seed plan.
    /// </summary>
    public bool Exhaustive { get; init; }

    /// <summary>Members per supervised batch child of an exhaustive campaign (<c>--batch-size</c>).</summary>
    public int BatchSize { get; init; } = DefaultBatchSize;

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

    /// <summary>
    /// Test seam over the batch child launch of an exhaustive campaign (the manifest path); default
    /// <see cref="SemanticSupervisor.SelfBatchWorker"/>. The batch supervisor itself is unchanged.
    /// </summary>
    public Func<string, SemanticBatchWorkerCommand>? BatchWorkerCommand { get; init; }

    /// <summary>Test seam: the campaign clock (elapsed time since start); default a stopwatch.</summary>
    public Func<TimeSpan>? Clock { get; init; }

    public bool Supervised => InProcessRunner is null;

    /// <summary>The seed plan's size (a seeded campaign; an exhaustive one plans its enumeration).</summary>
    public long PlannedCases => checked((long)(LastSeed - FirstSeed + 1) * CasesPerSeed);

    /// <summary>The bounds a campaign refuses to start without (null when valid).</summary>
    public string? Problem()
    {
        if (!SemanticCorpus.SeededRecipes.Contains(Recipe)) return "--recipe must be one of: " + SemanticCampaign.RecipeNames;
        if (Exhaustive)
        {
            if (!SemanticCorpus.FiniteRecipes.Contains(Recipe))
                return $"--exhaustive needs a finite recipe ({string.Join(", ", SemanticCorpus.FiniteRecipes)}); '{Recipe}' is not finite";
            if (BatchSize is < 1 or > MaxBatchSize) return $"--batch-size must be 1..{MaxBatchSize.ToString(CultureInfo.InvariantCulture)}";
        }
        else
        {
            if (LastSeed < FirstSeed) return "the seed range is empty (LAST < FIRST)";
            if (LastSeed - FirstSeed >= MaxSeedRange) return $"the seed range exceeds {MaxSeedRange.ToString(CultureInfo.InvariantCulture)} seeds";
            if (CasesPerSeed is < 1 or > MaxCasesPerSeed) return $"--cases-per-seed must be 1..{MaxCasesPerSeed.ToString(CultureInfo.InvariantCulture)}";
        }

        if (MaxCases < 1) return "--max-cases must be at least 1";
        if (MaxTime <= TimeSpan.Zero) return "--max-seconds must be at least 1";
        if (Deadline <= TimeSpan.Zero || Deadline.TotalMilliseconds > uint.MaxValue - 1)
            return "--deadline-seconds must be 1..4294967 (the supervisor timer range)";
        if (MaxAttempts < 0) return "--max-attempts must be non-negative";
        if (string.IsNullOrWhiteSpace(OutputDirectory)) return "--out must name a directory";
        return null;
    }
}

/// <summary>One failing case of a campaign, the recipe it was planned from, and what became of its reduction.</summary>
internal sealed record SemanticCampaignFailure(
    string CaseId,
    string Recipe,
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

    /// <summary>The original batch reproducer, retained even when a standalone rerun passes.</summary>
    public string? BatchManifest { get; init; }

    /// <summary>How the failure relates to its batch (<see cref="SemanticFailureClass"/>): standalone outside a batch.</summary>
    public string Classification { get; init; } = SemanticFailureClass.Standalone;

    /// <summary>The single-case rerun of a failure observed in a batch; <c>null</c> outside a batch.</summary>
    public SemanticCaseResult? StandaloneRerun { get; init; }

    /// <summary>The complete batch reproducer of a batch-only or batch-dependent failure: every preceding member, then this one.</summary>
    public string? BatchReproducer { get; init; }

    /// <summary>The sequence reduction of a batch-only or batch-dependent failure (<see cref="SemanticSequenceReducer"/>).</summary>
    public SemanticSequenceResult? Sequence { get; init; }

    /// <summary>The reduced sequence's manifest (the shortest reproducing prefix, then this case) and its record.</summary>
    public string? SequenceManifest { get; init; }

    public string? SequenceRecord { get; init; }

    /// <summary>The reduced program's context reproducer: the reduced prefix, then the reduced program (exact-source).</summary>
    public string? ReductionContext { get; init; }
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
    /// <summary>Distinct base sources among the executed cases: below <see cref="Executed"/>, the search revisited programs.</summary>
    public int DistinctSources { get; init; }

    /// <summary>Distinct (base source, execution profile) pairs among the executed cases.</summary>
    public int DistinctSourceProfiles { get; init; }

    /// <summary>An exhaustive campaign's choice sequences (its <see cref="Planned"/> counts the distinct programs); otherwise <c>null</c>.</summary>
    public int? Sequences { get; init; }

    /// <summary>An exhaustive campaign that executed every enumerated program.</summary>
    public bool Complete => Options.Exhaustive && Stop == SemanticCampaignStop.Completed && Executed == Planned;

    /// <summary>The failures per <see cref="SemanticFailureClass"/>, in its order.</summary>
    public ImmutableArray<(string Class, int Count)> Classifications
        => [.. SemanticFailureClass.All.Select(c => (c, Failures.Count(f => f.Classification == c)))];

    /// <summary>Failures that occur only in their batch (batch-only and batch-dependent).</summary>
    public int BatchFailures => Failures.Count(static f => f.Classification != SemanticFailureClass.Standalone);

    public string Describe()
    {
        var uncovered = FirstUncovered is null ? "" : " first-uncovered=" + FirstUncovered;
        var batchOnly = BatchFailures == 0 ? "" : string.Create(CultureInfo.InvariantCulture, $" batch-only={BatchFailures}");
        var plan = Options.Exhaustive
            ? string.Create(CultureInfo.InvariantCulture,
                $"exhaustive ({Planned} programs from {Sequences} choice sequences, {(Options.Supervised ? $"batches of {Options.BatchSize}" : "in process")})")
            : string.Create(CultureInfo.InvariantCulture, $"seeds {Options.FirstSeed:X}..{Options.LastSeed:X} x {Options.CasesPerSeed}");
        var complete = Options.Exhaustive ? " complete=" + (Complete ? "yes" : "no") : "";
        return string.Create(CultureInfo.InvariantCulture,
            $"semantic-campaign: recipe {Options.Recipe}, {plan}: planned={Planned} executed={Executed} passed={Passed} failed={Failures.Length}{batchOnly} distinct-sources={DistinctSources} distinct-source-profiles={DistinctSourceProfiles} stop={SemanticCampaign.StopName(Stop)}{complete}{uncovered} elapsed={Elapsed.TotalSeconds:F1}s");
    }
}

/// <summary>
/// <c>semantic-campaign</c> (SEM-2C, fuzz/README.md § Campaigns): a BOUNDED, deterministic search for
/// failing generated cases. It enumerates the ids <c>sem2b/v1/&lt;recipe&gt;/&lt;seed&gt;/&lt;index&gt;</c> of ONE
/// seeded recipe (<c>--recipe seed|seed-nested|seed-nested-wide|seed-nested-wider</c>, default <c>seed</c>;
/// <see cref="SemanticCorpus.SeededRecipes"/>) for every seed of an inclusive hex range and every
/// index below the cases-per-seed count, in that order, runs each under <see cref="SemanticSupervisor"/>
/// (recipe mode, one child at a time, the descriptor persisted before dispatch), persists every
/// failure with its signature, and — unless <c>--no-reduce</c> — reduces it with
/// <see cref="SemanticReducer"/> (supervised, exact-source candidates) and writes the reduced
/// artifacts. With <c>--exhaustive</c> the plan is instead EVERY program of a finite recipe
/// (<see cref="SemanticExhaustive"/>, ids <c>sem2b/v1/&lt;recipe&gt;/all/&lt;choices&gt;</c>), run in
/// supervised batches (one child per batch, every descriptor persisted before dispatch, every failing
/// member and the first member the batch could not answer rerun alone), with the same failure handling —
/// except that a failure the standalone rerun does not reproduce is classified batch-only (or
/// batch-dependent: another signature alone), keeps its complete batch reproducer, and is reduced first as
/// a sequence (<see cref="SemanticSequenceReducer"/>) and then as a program in that sequence. It stops at the first
/// exhausted budget and reports what it covered, including the distinct sources and (source,
/// profile) pairs executed. It writes only inside its own output directory, which must be new or empty.
/// </summary>
internal static class SemanticCampaign
{
    internal const string SummaryFormat = "kl-sem2c-campaign";
    internal const int SummaryFormatVersion = 1;
    internal const string SummaryFile = "campaign.json";
    internal const string SeededMode = "seeded";
    internal const string ExhaustiveMode = "exhaustive";

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

    /// <summary>The recipe names <c>--recipe</c> accepts, for messages.</summary>
    internal static string RecipeNames => string.Join(", ", SemanticCorpus.SeededRecipes);

    /// <summary>
    /// The planned (seed, index) pairs in campaign order (seed ascending, then index ascending); the
    /// recipe (<see cref="SemanticCampaignOptions.Recipe"/>) turns each pair into its case id.
    /// </summary>
    internal static IEnumerable<(ulong Seed, int Index)> Plan(SemanticCampaignOptions options)
    {
        for (var seed = options.FirstSeed; ; seed++)
        {
            for (var index = 0; index < options.CasesPerSeed; index++) yield return (seed, index);
            if (seed == options.LastSeed) yield break;
        }
    }

    /// <summary>The id of one planned case; the default recipe is the option's default.</summary>
    internal static string CaseId(ulong seed, int index, string recipe = SemanticCorpus.SeedRecipe)
        => SemanticCorpus.SeededBuilder(recipe, seed, index).CaseId;

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
        var sources = new HashSet<string>(StringComparer.Ordinal);
        var sourceProfiles = new HashSet<(string Source, string Profile)>();
        var stop = SemanticCampaignStop.Completed;
        string? firstUncovered = null;
        string? lastCovered = null;
        var timeExhausted = false;

        // Counts one executed case; a failure is persisted (descriptor with its result, and its
        // signature), classified against its batch (a batch-only failure also keeps its complete
        // batch reproducer) and then, unless --no-reduce, reduced: a standalone failure by the case's
        // own builder, a batch-only one first as a sequence, then as a program in its reduced context.
        void Record(SemanticCaseBuilder builder, SemanticCase semanticCase, SemanticCaseResult result, SemanticBatchContext? batch)
        {
            executed++;
            lastCovered = semanticCase.CaseId;
            verdicts[result.Verdict] = verdicts.GetValueOrDefault(result.Verdict) + 1;
            sources.Add(semanticCase.Source);
            // Count observed base profiles, including expected front-end refusals, rather than
            // claiming every requested profile when a worker died before writing any observation.
            foreach (var run in result.Runs.Where(static r => r.Member == SemanticMember.BaseRole))
                sourceProfiles.Add((semanticCase.Source, run.Profile));
            if (result.Passed)
            {
                passed++;
                return;
            }

            var signature = SemanticFailureSignature.Of(result);
            var classification = batch is null ? SemanticFailureClass.Standalone : SemanticFailureClass.Of(signature, batch.Standalone);
            Directory.CreateDirectory(failuresDir);
            var safe = SemanticReplay.SafeName(semanticCase.CaseId);
            var descriptor = Path.Combine(failuresDir, safe + ".json");
            var signatureFile = Path.Combine(failuresDir, safe + ".signature.json");
            File.WriteAllText(descriptor, SemanticDescriptor.Write(semanticCase, result));
            File.WriteAllText(signatureFile, WriteSignature(semanticCase.CaseId, options.Recipe, signature, result, classification));
            log.WriteLine($"FAILURE {semanticCase.CaseId}: [{signature}] {(result.Findings.IsEmpty ? "-" : result.Findings[0])}");
            log.WriteLine($"  descriptor={descriptor}");

            var failure = new SemanticCampaignFailure(semanticCase.CaseId, options.Recipe, result.Verdict, signature, Relative(outDir, descriptor),
                Relative(outDir, signatureFile), null, null, null, null, null, null, 0, 0, options.Reduce ? null : "disabled (--no-reduce)")
            {
                BatchManifest = batch is null ? null : Relative(outDir, batch.Manifest),
                Classification = classification,
                StandaloneRerun = batch?.Standalone,
            };
            if (batch is not null && classification != SemanticFailureClass.Standalone)
            {
                // The complete batch reproducer: every member that ran before this one, then this one.
                var reproducerDir = Path.Combine(failuresDir, safe + ".batch");
                ImmutableArray<SemanticCase> members = [.. batch.Prefix, semanticCase];
                var reproducer = SemanticBatchSequence.Persist(reproducerDir, members, SemanticReplay.Mode.Recipe);
                File.WriteAllText(Path.Combine(reproducerDir, "batch.json"), SemanticBatchSequence.WriteReproducerRecord(
                    options.Recipe, semanticCase.CaseId, classification, signature, batch.Standalone, Relative(outDir, batch.Manifest), members));
                failure = failure with { BatchReproducer = Relative(outDir, reproducer) };
                log.WriteLine(string.Create(CultureInfo.InvariantCulture,
                    $"  {classification}: standalone rerun {batch.Standalone.Verdict}; batch reproducer={reproducer} ({members.Length} members)"));
            }

            if (options.Reduce)
            {
                if (clock() >= options.MaxTime)
                {
                    timeExhausted = true;
                    failure = failure with { ReductionSkipped = "time budget exhausted" };
                }
                else if (classification == SemanticFailureClass.Standalone)
                {
                    failure = Reduce(builder, failure, Path.Combine(reducedDir, safe), outDir, options, clock, log);
                }
                else
                {
                    failure = ReduceInBatch(builder, semanticCase, batch!, failure, outDir, options, clock, log);
                }
            }

            failures.Add(failure);
        }

        // The budgets, checked before every case (an exhaustive batch: before every batch).
        bool Stopped(string nextCaseId)
        {
            if (timeExhausted || clock() >= options.MaxTime) stop = SemanticCampaignStop.TimeBudget;
            else if (executed >= options.MaxCases) stop = SemanticCampaignStop.CaseBudget;
            else return false;
            firstUncovered = nextCaseId;
            return true;
        }

        long planned;
        int? sequences = null;
        if (options.Exhaustive)
        {
            var enumeration = SemanticExhaustive.Enumerate(options.Recipe);
            planned = enumeration.Programs.Length;
            sequences = enumeration.Sequences;
            log.WriteLine(string.Create(CultureInfo.InvariantCulture,
                $"semantic-campaign: {options.Recipe} enumerates {enumeration.Programs.Length} distinct programs from {enumeration.Sequences} choice sequences"));
            var programs = enumeration.Programs;
            var next = 0;
            var batchNumber = 0;
            while (next < programs.Length && !Stopped(programs[next].CaseId))
            {
                if (options.InProcessRunner is { } inProcess)
                {
                    var builder = SemanticCorpus.ExhaustiveBuilder(options.Recipe, programs[next].Choices);
                    var semanticCase = builder.Build();
                    Record(builder, semanticCase, inProcess(semanticCase), null);
                    next++;
                    continue;
                }

                var size = Math.Min(options.BatchSize, Math.Min(programs.Length - next, options.MaxCases - executed));
                next += SuperviseBatch(programs.AsSpan(next, size).ToArray(), ++batchNumber, workDir, options, Record, log);
            }
        }
        else
        {
            planned = options.PlannedCases;
            foreach (var (seed, index) in Plan(options))
            {
                var builder = SemanticCorpus.SeededBuilder(options.Recipe, seed, index);
                if (Stopped(builder.CaseId)) break;
                var semanticCase = builder.Build();
                Record(builder, semanticCase, options.InProcessRunner is { } runner ? runner(semanticCase) : Supervise(semanticCase, workDir, options), null);
            }
        }

        var outcome = new SemanticCampaignResult(options, planned, executed, passed, stop, firstUncovered, lastCovered,
            verdicts.ToImmutableSortedDictionary(), [.. failures], clock())
        {
            DistinctSources = sources.Count,
            DistinctSourceProfiles = sourceProfiles.Count,
            Sequences = sequences,
        };
        File.WriteAllText(Path.Combine(outDir, SummaryFile), WriteSummary(outcome));
        if (Directory.Exists(workDir) && !Directory.EnumerateFileSystemEntries(workDir).Any()) Directory.Delete(workDir);
        return outcome;
    }

    /// <summary>
    /// One supervised batch of an exhaustive campaign: every member's descriptor is persisted under
    /// <c>work/</c> BEFORE the manifest is written and the child dispatched, the child replays them in
    /// order (<see cref="SemanticSupervisor.RunBatch"/>), and each member with a result is recorded in
    /// order. Every failing member, and the first member WITHOUT a result (in flight when the child
    /// crashed or timed out, or one the child could not replay), also runs ALONE under the single-case
    /// supervisor, which keeps its evidence exactly as a seeded campaign does; the original batch
    /// failure is recorded whatever that rerun gives, and the rerun classifies it
    /// (<see cref="SemanticFailureClass"/>) with the members before it as its context. The members
    /// after a member without a result are left for the next batch. A failing batch's
    /// entire manifest, descriptors, results and supervision record are kept together; a clean,
    /// passing batch's evidence is removed. Returns how many members were recorded.
    /// </summary>
    private static int SuperviseBatch(
        SemanticExhaustive.EnumeratedProgram[] programs, int batchNumber, string workDir, SemanticCampaignOptions options,
        Action<SemanticCaseBuilder, SemanticCase, SemanticCaseResult, SemanticBatchContext?> record, TextWriter log)
    {
        Directory.CreateDirectory(workDir);
        var stem = "batch-" + batchNumber.ToString("D5", CultureInfo.InvariantCulture);
        var batchDir = Directory.CreateDirectory(Path.Combine(workDir, stem)).FullName;
        var builders = programs.Select(p => SemanticCorpus.ExhaustiveBuilder(options.Recipe, p.Choices)).ToArray();
        var members = new List<SemanticBatchMember>();
        foreach (var builder in builders)
        {
            var semanticCase = builder.Build();
            var descriptor = Path.Combine(batchDir, SemanticReplay.SafeName(semanticCase.CaseId) + ".json");
            File.WriteAllText(descriptor, SemanticDescriptor.Write(semanticCase));
            members.Add(new SemanticBatchMember(semanticCase, descriptor, descriptor + ".result.json"));
        }

        var manifest = Path.Combine(workDir, stem + ".txt");
        SemanticSupervisor.WriteManifest(manifest, members.Select(static m => (m.DescriptorPath, m.ResultPath)));
        var command = (options.BatchWorkerCommand ?? SemanticSupervisor.SelfBatchWorker)(manifest);
        var run = SemanticSupervisor.RunBatch(command, members, options.Deadline);
        if (run.ChildFailure is { } childFailure)
            log.WriteLine($"  batch {batchNumber.ToString(CultureInfo.InvariantCulture)}: {childFailure} ({run.Detail}); manifest={manifest}");

        // Decide before removing anything: a batch-only defect may depend on every preceding case.
        var keep = run.ChildFailure is not null || run.Members.Any(static m => m.Verdict != SemanticVerdict.Passed);
        var cases = run.Members.Select(static m => m.Case).ToImmutableArray();
        var recorded = 0;
        while (recorded < run.Members.Length)
        {
            var member = run.Members[recorded];
            // The member's result as judged; the child's own failure for the final member when the child
            // died after writing it (its semantic result file retained); the child's failure (or a
            // missing observation) for a member without a result.
            var result = SemanticBatchSequence.MemberResult(run, recorded);
            SemanticBatchContext? context = null;
            if (!result.Passed)
            {
                // Every failure observed in a batch also runs ALONE: one that depends on an earlier
                // member is classified batch-only instead of falling through as "not reproduced".
                var rerunDir = Path.Combine(batchDir, "rerun");
                var alone = Supervise(member.Case, rerunDir, options);
                if (Directory.Exists(rerunDir) && !Directory.EnumerateFileSystemEntries(rerunDir).Any()) Directory.Delete(rerunDir);
                log.WriteLine($"  batch member {member.Case.CaseId}: standalone rerun {alone.Verdict}{(member.Verdict is null ? "; original batch failure retained" : "")}; manifest={manifest}");
                context = new SemanticBatchContext(manifest, cases[..recorded], alone);
            }

            record(builders[recorded++], member.Case, result, context);
            if (member.Verdict is null) break; // the members after one without a result go to the next batch
        }

        if (!keep)
        {
            foreach (var member in run.Members)
            {
                TryDelete(member.DescriptorPath);
                TryDelete(member.ResultPath);
            }
            if (!Directory.EnumerateFileSystemEntries(batchDir).Any()) Directory.Delete(batchDir);
            TryDelete(manifest);
            TryDelete(manifest + ".supervision.txt");
        }

        return recorded;
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

    /// <summary>
    /// Reduces a batch-only or batch-dependent failure in two steps, each candidate one fresh batch child
    /// (<see cref="SemanticCampaignOptions.BatchWorkerCommand"/>) that runs a prefix and then the failing
    /// case: first the SEQUENCE — the members before it shrink while the failure (its signature, the child
    /// reaching it) recurs (<see cref="SemanticSequenceReducer"/>), the reduced sequence persisted under
    /// <c>reduced/&lt;case&gt;.sequence/</c>; then the PROGRAM in that reduced context, by the case's own
    /// builder (<see cref="SemanticReducer"/>, exact-source candidates), its artifacts under
    /// <c>reduced/&lt;case&gt;/</c> and its context reproducer under <c>reduced/&lt;case&gt;.sequence/program/</c>.
    /// Each step is bounded by <see cref="SemanticCampaignOptions.MaxAttempts"/> executions and the time budget.
    /// </summary>
    private static SemanticCampaignFailure ReduceInBatch(
        SemanticCaseBuilder builder, SemanticCase failing, SemanticBatchContext batch, SemanticCampaignFailure failure, string outDir,
        SemanticCampaignOptions options, Func<TimeSpan> clock, TextWriter log)
    {
        var safe = SemanticReplay.SafeName(failing.CaseId);
        var sequenceDir = Path.Combine(outDir, "reduced", safe + ".sequence");
        var evidence = Path.Combine(sequenceDir, "evidence");
        var command = options.BatchWorkerCommand ?? SemanticSupervisor.SelfBatchWorker;
        bool ShouldStop() => clock() >= options.MaxTime;
        var executions = 0;

        // One candidate in a fresh batch child: the last member's recorded result, or null when the
        // child never reached it. The persisted reproducers are written separately, so a judged
        // candidate's scratch directory is removed.
        SemanticCaseResult? RunAfter(IReadOnlyList<SemanticCase> prefix, SemanticCase last, SemanticReplay.Mode mode)
        {
            var dir = Path.Combine(evidence, "run-" + (++executions).ToString("D4", CultureInfo.InvariantCulture));
            try
            {
                return SemanticBatchSequence.LastResult(SemanticBatchSequence.Run(
                    SemanticBatchSequence.Persist(dir, [.. prefix, last], mode), command, options.Deadline));
            }
            finally
            {
                SemanticBatchSequence.TryDeleteDirectory(dir);
            }
        }

        try
        {
            var sequence = SemanticSequenceReducer.Reduce(
                batch.Prefix,
                prefix => RunAfter(prefix, failing, SemanticReplay.Mode.Recipe) is { } recurred && SemanticFailureSignature.Of(recurred) == failure.Signature,
                options.MaxAttempts,
                ShouldStop);
            log.WriteLine("  sequence: " + sequence.Describe());
            failure = failure with { Sequence = sequence };
            if (sequence.Status == SemanticSequenceStatus.NotReproduced)
            {
                return failure with
                {
                    ReductionSkipped = sequence.Stopped ? "time budget exhausted"
                        : sequence.AttemptLimitReached ? "no execution left (--max-attempts)"
                        : "the batch failure did not reproduce in a fresh batch child",
                    ReductionStopped = sequence.Stopped ? "time budget exhausted" : null,
                };
            }

            var manifest = SemanticBatchSequence.Persist(sequenceDir, [.. sequence.Reduced, failing], SemanticReplay.Mode.Recipe);
            var record = Path.Combine(sequenceDir, "sequence.json");
            File.WriteAllText(record, SemanticBatchSequence.WriteSequenceRecord(failing.CaseId, failure.Signature, sequence));
            failure = failure with { SequenceManifest = Relative(outDir, manifest), SequenceRecord = Relative(outDir, record) };
            log.WriteLine(string.Create(CultureInfo.InvariantCulture, $"  reduced sequence={manifest} ({sequence.Reduced.Length} preceding member(s))"));
            if (sequence.Stopped || ShouldStop())
                return failure with { ReductionSkipped = "time budget exhausted", ReductionStopped = "time budget exhausted" };

            // The program itself, after the reduced prefix (exact-source: a candidate is not a recipe case).
            var reduction = new SemanticReductionOptions
            {
                MaxAttempts = options.MaxAttempts,
                Supervised = true,
                RequiredSignature = failure.Signature,
                ShouldStop = ShouldStop,
                Runner = c => RunAfter(sequence.Reduced, c, SemanticReplay.Mode.ExactSource)
                    ?? new SemanticCaseResult(c.CaseId, SemanticVerdict.HarnessFailure, ["the batch child did not reach the candidate"], [], SemanticPath.None, [], []),
            };
            var result = SemanticReducer.Reduce(builder, reduction);
            log.WriteLine("  reduce in context: " + result.Describe());
            if (result.Status == SemanticReductionStatus.NothingToReduce)
            {
                return failure with
                {
                    ReductionStatus = result.Status.ToString(),
                    ReductionSkipped = "the failure did not reproduce after the reduced prefix (observed " + result.Signature + ")",
                    ReductionAttempts = result.Attempts,
                };
            }

            var (stem, reduced) = SemanticReduction.WriteArtifacts(result, Path.Combine(outDir, "reduced", safe));
            var context = SemanticBatchSequence.Persist(Path.Combine(sequenceDir, "program"), [.. sequence.Reduced, reduced], SemanticReplay.Mode.ExactSource);
            log.WriteLine($"  reduced={stem}.json ({reduced.Source.Length.ToString(CultureInfo.InvariantCulture)} source characters) in context={context}");
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
                ReductionContext = Relative(outDir, context),
            };
        }
        finally
        {
            if (Directory.Exists(evidence) && !Directory.EnumerateFileSystemEntries(evidence).Any()) Directory.Delete(evidence);
        }
    }

    // ── Summary ─────────────────────────────────────────────────────────────

    /// <summary>
    /// The <c>kl-sem2c-campaign</c> v1 summary. It names the plan (recipe, seed range, cases per seed),
    /// the bounds, what was covered and every failure with its recipe and artifacts (paths relative to
    /// the output directory, <c>/</c>-separated). It carries no clock reading and no absolute path, so
    /// for a fixed recipe, seed range and bounds a campaign stopped by its case budget (or completed)
    /// writes the same bytes on every run. <c>recipe</c> (on the summary, on each failure and in the
    /// signature sidecar) is an ADDITIVE v1 field: a document without it was written before
    /// <c>--recipe</c> existed and describes a <c>seed</c> campaign. <c>mode</c>
    /// (<c>seeded</c>/<c>exhaustive</c>), <c>distinctSources</c> and <c>distinctSourceProfiles</c> are
    /// additive v1 fields as well (a document without <c>mode</c> is seeded). An exhaustive summary
    /// writes <c>null</c> seeds and cases per seed, its <c>batchSize</c>, the enumeration's choice
    /// <c>sequences</c> (its <c>planned</c> count is the distinct programs), <c>null</c> for an
    /// unbounded <c>maxCases</c>, and <c>complete</c>: every enumerated program executed.
    /// <c>classifications</c> (failures per <see cref="SemanticFailureClass"/>) and, on each failure,
    /// <c>classification</c> are additive v1 fields too (absent: every failure is standalone); a failure
    /// observed in a batch adds its <c>standalone</c> rerun, and a batch-only or batch-dependent one its
    /// complete <c>batchReproducer</c> manifest and its <c>sequenceReduction</c> (status, prefix lengths,
    /// executions, the reduced sequence's manifest and record), with the reduced program's
    /// <c>reduction.context</c> manifest.
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
            w.WriteString("recipe", o.Recipe);
            w.WriteString("mode", o.Exhaustive ? ExhaustiveMode : SeededMode);
            if (o.Exhaustive)
            {
                w.WriteNull("firstSeed");
                w.WriteNull("lastSeed");
                w.WriteNull("casesPerSeed");
                w.WriteNumber("batchSize", o.BatchSize);
                if (result.Sequences is { } sequences) w.WriteNumber("sequences", sequences);
                else w.WriteNull("sequences");
            }
            else
            {
                w.WriteString("firstSeed", o.FirstSeed.ToString("X", CultureInfo.InvariantCulture));
                w.WriteString("lastSeed", o.LastSeed.ToString("X", CultureInfo.InvariantCulture));
                w.WriteNumber("casesPerSeed", o.CasesPerSeed);
            }

            if (o.Exhaustive && o.MaxCases == int.MaxValue) w.WriteNull("maxCases"); // unbounded
            else w.WriteNumber("maxCases", o.MaxCases);
            w.WriteNumber("maxSeconds", (long)Math.Ceiling(o.MaxTime.TotalSeconds));
            w.WriteNumber("deadlineSeconds", (long)Math.Ceiling(o.Deadline.TotalSeconds));
            w.WriteBoolean("reduce", o.Reduce);
            w.WriteNumber("maxAttempts", o.MaxAttempts);
            w.WriteBoolean("supervised", o.Supervised);
            w.WriteNumber("planned", result.Planned);
            w.WriteNumber("executed", result.Executed);
            w.WriteNumber("passed", result.Passed);
            w.WriteNumber("failed", result.Failures.Length);
            w.WriteNumber("distinctSources", result.DistinctSources);
            w.WriteNumber("distinctSourceProfiles", result.DistinctSourceProfiles);
            if (o.Exhaustive) w.WriteBoolean("complete", result.Complete);
            w.WriteStartObject("classifications");
            foreach (var (name, count) in result.Classifications) w.WriteNumber(name, count);
            w.WriteEndObject();
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
                w.WriteString("recipe", f.Recipe);
                w.WriteString("verdict", f.Verdict.ToString());
                WriteSignatureObject(w, f.Signature);
                w.WriteString("descriptor", f.Descriptor);
                w.WriteString("signatureFile", f.SignatureFile);
                w.WriteString("classification", f.Classification);
                if (f.BatchManifest is { } batchManifest) w.WriteString("batchManifest", batchManifest);
                if (f.StandaloneRerun is { } alone)
                {
                    w.WriteStartObject("standalone");
                    w.WriteString("verdict", alone.Verdict.ToString());
                    WriteSignatureObject(w, SemanticFailureSignature.Of(alone));
                    w.WriteEndObject();
                }

                if (f.BatchReproducer is { } reproducer) w.WriteString("batchReproducer", reproducer);
                if (f.Sequence is { } sequence)
                {
                    w.WriteStartObject("sequenceReduction");
                    w.WriteString("status", sequence.Status.ToString());
                    w.WriteNumber("originalPrefix", sequence.Original.Length);
                    w.WriteNumber("reducedPrefix", sequence.Reduced.Length);
                    w.WriteNumber("attempts", sequence.Attempts);
                    w.WriteBoolean("attemptLimitReached", sequence.AttemptLimitReached);
                    w.WriteBoolean("stopped", sequence.Stopped);
                    WriteNullable(w, "manifest", f.SequenceManifest);
                    WriteNullable(w, "record", f.SequenceRecord);
                    w.WriteEndObject();
                }

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
                if (f.ReductionContext is { } context) w.WriteString("context", context);
                w.WriteEndObject();
                w.WriteEndObject();
            }

            w.WriteEndArray();
            w.WriteEndObject();
        }

        return Encoding.UTF8.GetString(stream.ToArray()) + "\n";
    }

    /// <summary>The per-failure signature sidecar: the case id, its recipe, the signature, the first finding and (additive) the failure's class.</summary>
    internal static string WriteSignature(
        string caseId, string recipe, SemanticFailureSignature signature, SemanticCaseResult result, string classification = SemanticFailureClass.Standalone)
    {
        using var stream = new MemoryStream();
        using (var w = new Utf8JsonWriter(stream, WriterOptions))
        {
            w.WriteStartObject();
            w.WriteString("format", SummaryFormat + "-signature");
            w.WriteNumber("formatVersion", SummaryFormatVersion);
            w.WriteString("caseId", caseId);
            w.WriteString("recipe", recipe);
            WriteSignatureObject(w, signature);
            WriteNullable(w, "firstFinding", result.Findings.IsDefaultOrEmpty ? null : result.Findings[0]);
            w.WriteString("classification", classification);
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

    internal static readonly string Usage =
        "usage: semantic-campaign --seeds FIRST[..LAST] [--recipe " + string.Join("|", SemanticCorpus.SeededRecipes) + "] " +
        "[--cases-per-seed N] [--max-cases N] [--max-seconds N] [--deadline-seconds N] [--max-attempts N] [--no-reduce] [--out DIR]\n" +
        "       semantic-campaign --exhaustive --recipe " + string.Join("|", SemanticCorpus.FiniteRecipes) + " " +
        "[--batch-size N] [--max-cases N] [--max-seconds N] [--deadline-seconds N] [--max-attempts N] [--no-reduce] [--out DIR]";

    /// <summary>
    /// <c>semantic-campaign</c>. Exit codes: 0 — every executed case passed (the summary says whether
    /// the plan was covered or a budget stopped it — for <c>--exhaustive</c>, whether it is
    /// <c>complete</c>); 1 — at least one failure (persisted, and reduced unless <c>--no-reduce</c>),
    /// or a reduction observed a generator precondition failure; 2 — usage (including
    /// <c>--exhaustive</c> for a recipe that is not finite), a refused output directory, or no case
    /// executed.
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
        var recipe = SemanticCorpus.SeedRecipe;
        int? casesPerSeed = null;
        int? maxCases = null;
        int? maxSeconds = null;
        var deadlineSeconds = (int)SemanticSupervisor.DefaultDeadline.TotalSeconds;
        var maxAttempts = SemanticCampaignOptions.DefaultMaxAttempts;
        int? batchSize = null;
        var reduce = true;
        var exhaustive = false;
        string? outDir = null;
        for (var i = 1; i < args.Length; i++)
        {
            var arg = args[i];
            if (arg == "--no-reduce")
            {
                reduce = false;
                continue;
            }

            if (arg == "--exhaustive")
            {
                exhaustive = true;
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
                case "--recipe":
                    if (!SemanticCorpus.SeededRecipes.Contains(value))
                    {
                        problem = $"--recipe '{value}' is not one of: {RecipeNames}";
                        return false;
                    }

                    recipe = value;
                    break;
                case "--cases-per-seed" when TryCount(value, out var count):
                    casesPerSeed = count;
                    break;
                case "--max-cases" when TryCount(value, out var count):
                    maxCases = count;
                    break;
                case "--max-seconds" when TryCount(value, out var count):
                    maxSeconds = count;
                    break;
                case "--batch-size" when TryCount(value, out var count):
                    batchSize = count;
                    break;
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

        if (exhaustive)
        {
            if (first is not null || casesPerSeed is not null)
            {
                problem = "--exhaustive enumerates the whole recipe: --seeds and --cases-per-seed do not apply";
                return false;
            }
        }
        else
        {
            if (batchSize is not null)
            {
                problem = "--batch-size applies only to --exhaustive";
                return false;
            }

            if (first is null || last is null)
            {
                problem = "--seeds is required (or --exhaustive for a finite recipe)";
                return false;
            }
        }

        var perSeed = casesPerSeed ?? SemanticCampaignOptions.DefaultCasesPerSeed;
        options = new SemanticCampaignOptions
        {
            FirstSeed = first ?? 0,
            LastSeed = last ?? 0,
            Recipe = recipe,
            Exhaustive = exhaustive,
            BatchSize = batchSize ?? SemanticCampaignOptions.DefaultBatchSize,
            CasesPerSeed = perSeed,
            MaxCases = maxCases ?? (exhaustive ? int.MaxValue : SemanticCampaignOptions.DefaultMaxCases),
            MaxTime = TimeSpan.FromSeconds(maxSeconds ?? (exhaustive ? SemanticCampaignOptions.DefaultExhaustiveMaxSeconds : SemanticCampaignOptions.DefaultMaxSeconds)),
            Deadline = TimeSpan.FromSeconds(deadlineSeconds),
            MaxAttempts = maxAttempts,
            Reduce = reduce,
            OutputDirectory = outDir ?? (exhaustive
                ? DefaultOutputDirectory(recipe + "-" + ExhaustiveMode)
                : DefaultOutputDirectory(first!.Value, last!.Value, perSeed, recipe)),
        };
        problem = "";
        return true;
    }

    /// <summary>
    /// <c>&lt;repository&gt;/artifacts/semantic-campaign/&lt;FIRST&gt;-&lt;LAST&gt;x&lt;N&gt;-&lt;UTC stamp&gt;</c> (git-ignored)
    /// when the current directory is inside a checkout, otherwise under the temporary directory. The
    /// default <c>seed</c> recipe keeps that name; any other recipe prefixes it
    /// (<c>seed-nested-&lt;FIRST&gt;-…</c>), so two recipes over one range never share a directory. An
    /// exhaustive campaign's is <c>&lt;recipe&gt;-exhaustive-&lt;UTC stamp&gt;</c>.
    /// </summary>
    internal static string DefaultOutputDirectory(ulong first, ulong last, int casesPerSeed, string recipe)
    {
        var prefix = recipe == SemanticCorpus.SeedRecipe ? "" : recipe + "-";
        return DefaultOutputDirectory(string.Create(CultureInfo.InvariantCulture, $"{prefix}{first:X}-{last:X}x{casesPerSeed}"));
    }

    private static string DefaultOutputDirectory(string plan)
    {
        var name = string.Create(CultureInfo.InvariantCulture, $"{plan}-{DateTime.UtcNow:yyyyMMdd'T'HHmmss'Z'}");
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
