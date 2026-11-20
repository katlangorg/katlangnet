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
/// </summary>
public class OutputRowCountsCorpusSweepTests(ITestOutputHelper output)
{
    private const long Seed = 11;

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

        foreach (var (id, source) in OutputRowCountsTestSupport.CorpusSources)
        {
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

        output.WriteLine($"{successes} corpus programs succeeded on at least one route; "
            + $"{stackHeadroomDifferences.Count} route-dependent stack-headroom difference(s) allowed.");
        foreach (var difference in stackHeadroomDifferences)
            output.WriteLine("allowed: " + difference);

        Assert.True(successes > 300, $"only {successes} corpus programs succeeded; the sweep is not exercising the corpora");
        Assert.True(spreadRows > 0, "no successful corpus program has a spread root row");
        Assert.True(rowsOfSeveral > 0, "no successful corpus program has a root row that produced several output rows");
        Assert.True(
            failures.Count == 0,
            $"{failures.Count} corpus result(s) break the partition or fail on one route while another succeeds:\n"
            + string.Join("\n", failures.Take(20)));
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

    private static string Describe(KatLangError error)
        => string.Create(CultureInfo.InvariantCulture, $"{error.Code} @ {error.Span?.ToString() ?? "-"}: {error.Message}");
}
