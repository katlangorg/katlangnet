using System.Globalization;
using Xunit.Abstractions;
using static KatLang.Tests.RootOutputRowCounts.OutputRowCountsTestSupport;

namespace KatLang.Tests.RootOutputRowCounts;

/// <summary>
/// THE PARTITION SWEEP: every program of both differential corpora (the canonical language spec
/// with its probes, and the semantic-explorer corpus) that succeeds must carry a complete
/// partition — one count per row of the elaborated root's output, no negative count, a sum equal
/// to the presented output rows, and exactly one for every row that is not a spread — on the
/// synchronous engine, the asynchronous engine, and the engine's async twin, and the routes that
/// succeed must agree on it.
/// <para><b>Routes succeed together.</b> A program that succeeds on one route must succeed on the
/// other two: a route that fails there is a finding, reported with the corpus case, the route and
/// its structured errors, so a route that lost its result cannot pass as "nothing to check". The
/// one exception is the documented route-dependent host-stack verdict
/// (<see cref="KatLangErrorCode.EvaluationStackExhausted"/>; <see cref="KatLangEngine.RunAsync(string, RunOptions?)"/>
/// explains why the twin route may go deeper or stop sooner than the synchronous one), recognized
/// by that structured code and never by message text; the routes that did succeed are still
/// checked and compared. A program that succeeds on no route carries no partition and is
/// skipped.</para>
/// <para><b>Shards.</b> The sweep runs three engine routes for every corpus program, minutes of
/// work in one test, so the corpus is split into <see cref="ShardCount"/> interleaved shards
/// (program <c>i</c> of <see cref="OutputRowCountsTestSupport.CorpusSources"/> in shard
/// <c>i mod ShardCount</c>), one test class each, which xUnit runs in parallel. Every shard checks
/// its programs exactly as the single sweep did, with the same failure messages. The coverage
/// guards — more than 300 successful programs, a spread root row, and a root row that produced
/// several output rows — are about the whole corpora, so they are checked once, on the totals of
/// all shards, by the shard that finishes last.</para>
/// </summary>
public abstract class OutputRowCountsCorpusSweepTests(ITestOutputHelper output, int shard)
{
    /// <summary>The number of shards; each has a concrete class below.</summary>
    internal const int ShardCount = 4;

    private const long Seed = 11;

    private static readonly CorpusTally Tally = new();

    [Fact]
    public async Task EverySuccessfulCorpusProgram_CarriesACompletePartition_OnEveryEngineRoute()
    {
        // One seed for the three runs of a program, so a random draw cannot make them differ.
        var pause = new Pause();
        var options = new RunOptions { RandomSeed = Seed };
        var twinOptions = new RunOptions { RandomSeed = Seed, HostOperations = pause.Operations() };
        var failures = new List<string>();
        var stackHeadroomDifferences = new List<string>();
        var successes = 0;
        var spreadRows = 0;
        var rowsOfSeveral = 0;
        var programs = 0;
        var watch = System.Diagnostics.Stopwatch.StartNew();

        var sources = OutputRowCountsTestSupport.CorpusSources;
        for (var index = shard; index < sources.Count; index += ShardCount)
        {
            var (id, source) = sources[index];
            programs++;
            (string Route, RunResult Result)[] runs =
            [
                ("sync", KatLangEngine.Run(source, options)),
                ("async", await KatLangEngine.RunAsync(source, options)),
                ("twin", await KatLangEngine.RunAsync(source, twinOptions)),
            ];

            // Every successful route carries the partition, and the successful routes agree on it.
            RunResult.Success? firstSuccess = null;
            var firstSuccessRoute = "";
            foreach (var (route, result) in runs)
            {
                if (result is not RunResult.Success success)
                    continue;

                if (PartitionProblem(success) is { } problem)
                    failures.Add($"{id} [{route}]: {problem}");

                if (firstSuccess is not null)
                {
                    if (!firstSuccess.OutputRowCounts.SequenceEqual(success.OutputRowCounts))
                    {
                        failures.Add(
                            $"{id} [{route}]: the partition [{string.Join(", ", success.OutputRowCounts)}] differs from "
                            + $"[{string.Join(", ", firstSuccess.OutputRowCounts)}] on [{firstSuccessRoute}]");
                    }

                    continue;
                }

                firstSuccess = success;
                firstSuccessRoute = route;
                successes++;
                for (var row = 0; row < success.Root.Output.Count && row < success.OutputRowCounts.Count; row++)
                {
                    if (success.Root.Output[row] is Expr.SequenceSpread)
                    {
                        spreadRows++;
                        if (success.OutputRowCounts[row] > 1)
                            rowsOfSeveral++;
                    }
                }
            }

            if (firstSuccess is null)
                continue;

            // One route succeeded, so the others must: an ordinary failure beside a success is a finding.
            foreach (var (route, result) in runs)
            {
                if (result is RunResult.Success)
                    continue;

                var difference = $"{id} [{route}]: {Describe(result)} (while [{firstSuccessRoute}] succeeded)";
                if (IsStackHeadroom(result))
                    stackHeadroomDifferences.Add(difference);
                else
                    failures.Add(difference);
            }
        }

        output.WriteLine($"shard {shard + 1} of {ShardCount} ({programs} of {sources.Count} programs, "
            + $"{watch.Elapsed.TotalSeconds:F1} s): {successes} corpus programs succeeded on at least one route; "
            + $"{stackHeadroomDifferences.Count} route-dependent stack-headroom difference(s) allowed.");
        foreach (var difference in stackHeadroomDifferences)
            output.WriteLine("allowed: " + difference);

        // The coverage guards are about the whole corpora: the last shard checks the totals.
        if (Tally.Add(successes, spreadRows, rowsOfSeveral) is { } total)
        {
            output.WriteLine($"all {ShardCount} shards: {total.Successes} corpus programs succeeded on at least one route.");
            Assert.True(total.Successes > 300, $"only {total.Successes} corpus programs succeeded; the sweep is not exercising the corpora");
            Assert.True(total.SpreadRows > 0, "no successful corpus program has a spread root row");
            Assert.True(total.RowsOfSeveral > 0, "no successful corpus program has a root row that produced several output rows");
        }

        Assert.True(
            failures.Count == 0,
            $"{failures.Count} corpus result(s) break the partition or fail on one route while another succeeds:\n"
            + string.Join("\n", failures.Take(20)));
    }

    /// <summary>
    /// The shards' coverage counts. <see cref="Add"/> returns the totals to the shard that completes
    /// the set, and null to the others; a run that does not execute every shard checks no totals.
    /// </summary>
    private sealed class CorpusTally
    {
        private readonly Lock _gate = new();
        private int _shards;
        private (int Successes, int SpreadRows, int RowsOfSeveral) _total;

        public (int Successes, int SpreadRows, int RowsOfSeveral)? Add(int successes, int spreadRows, int rowsOfSeveral)
        {
            lock (_gate)
            {
                _total = (_total.Successes + successes, _total.SpreadRows + spreadRows, _total.RowsOfSeveral + rowsOfSeveral);
                return ++_shards == ShardCount ? _total : null;
            }
        }
    }

    /// <summary>
    /// The documented route-dependent outcome: an evaluation failure whose every error is the
    /// host-stack verdict, decided by the structured code.
    /// </summary>
    private static bool IsStackHeadroom(RunResult result)
        => result is RunResult.EvalFailure { Errors.Count: > 0 } failure
            && failure.Errors.All(static error => error.Code == KatLangErrorCode.EvaluationStackExhausted);

    /// <summary>The variant of a result and, when it is not a success, every structured error it carries.</summary>
    private static string Describe(RunResult result)
        => result switch
        {
            RunResult.Success => "Success",
            RunResult.NoProgramOutput none => "NoProgramOutput: " + Describe(none.Diagnostic),
            RunResult.ParseFailure parse => "ParseFailure: " + string.Join(" | ", parse.Errors.Select(Describe)),
            RunResult.EvalFailure failure => "EvalFailure: " + string.Join(" | ", failure.Errors.Select(Describe)),
        };

    /// <summary>This sweep's shard (see the class summary).</summary>
    internal int Shard => shard;

    private static string Describe(KatLangError error)
        => string.Create(CultureInfo.InvariantCulture, $"{error.Code} @ {error.Span?.ToString() ?? "-"}: {error.Message}");
}

// The shards of the partition sweep, one class each so that xUnit runs them in parallel.
public sealed class OutputRowCountsCorpusSweepShard1Tests(ITestOutputHelper output) : OutputRowCountsCorpusSweepTests(output, shard: 0);

public sealed class OutputRowCountsCorpusSweepShard2Tests(ITestOutputHelper output) : OutputRowCountsCorpusSweepTests(output, shard: 1);

public sealed class OutputRowCountsCorpusSweepShard3Tests(ITestOutputHelper output) : OutputRowCountsCorpusSweepTests(output, shard: 2);

public sealed class OutputRowCountsCorpusSweepShard4Tests(ITestOutputHelper output) : OutputRowCountsCorpusSweepTests(output, shard: 3);

/// <summary>
/// The sweep's shard classes are exactly shards 0 to <see cref="OutputRowCountsCorpusSweepTests.ShardCount"/> - 1, each
/// once: a missing shard would leave its programs unchecked and the corpus totals unchecked with them.
/// </summary>
public class OutputRowCountsCorpusSweepShardingTests
{
    [Fact]
    public void TheShardClasses_CoverEveryShardOnce()
    {
        var shards = typeof(OutputRowCountsCorpusSweepTests).Assembly.GetTypes()
            .Where(static type => type.IsSubclassOf(typeof(OutputRowCountsCorpusSweepTests)) && !type.IsAbstract)
            .Select(static type => ((OutputRowCountsCorpusSweepTests)Activator.CreateInstance(type, new object?[] { null })!).Shard)
            .Order()
            .ToArray();
        Assert.Equal(Enumerable.Range(0, OutputRowCountsCorpusSweepTests.ShardCount), shards);
    }
}
