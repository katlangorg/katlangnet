using KatLang.Benchmarks;

namespace KatLang.Tests.Infrastructure;

/// <summary>
/// Pins the benchmark host's exit-code decision (<c>benchmarks/KatLang.Benchmarks/BenchmarkHostExit.cs</c>,
/// compiled into this assembly as shared source). BenchmarkDotNet never fails the process itself, so a run
/// whose every benchmark ended as <c>NA</c> used to exit 0 and could be cited as performance evidence.
/// The mapping from BenchmarkDotNet's summaries and arguments onto these inputs lives in the host
/// (<c>BenchmarkHostRun</c>) and is exercised by real runs, not here.
/// </summary>
public class BenchmarkHostExitTests
{
    private static BenchmarkSummaryOutcome Summary(int cases, int successful, int critical = 0, string title = "Run")
        => new(title, cases, successful, critical);

    [Fact]
    public void ExitCodes_AreTheDocumentedValues()
    {
        Assert.Equal(0, BenchmarkHostExit.Success);
        Assert.Equal(1, BenchmarkHostExit.NoSuccessfulBenchmark);
        Assert.Equal(2, BenchmarkHostExit.NoBenchmarkRun);
    }

    [Theory]
    [InlineData(1, 1)]
    [InlineData(8, 8)]
    public void EveryCaseSucceeded_ExitsZeroSilently(int cases, int successful)
    {
        var exit = BenchmarkHostExit.Decide(runRequested: true, [Summary(cases, successful)]);

        Assert.Equal(new BenchmarkHostExit(BenchmarkHostExit.Success, null), exit);
    }

    [Theory]
    [InlineData(1)]
    [InlineData(8)]
    public void NoCaseSucceeded_ExitsNonzeroWithTheCount(int cases)
    {
        var exit = BenchmarkHostExit.Decide(runRequested: true, [Summary(cases, successful: 0)]);

        Assert.Equal(BenchmarkHostExit.NoSuccessfulBenchmark, exit.ExitCode);
        Assert.Equal($"none of the {cases} benchmark case(s) produced a successful report (every result is NA).", exit.Message);
    }

    [Fact]
    public void NoCaseSucceeded_AcrossSeveralSummaries_ExitsNonzero()
    {
        var exit = BenchmarkHostExit.Decide(runRequested: true, [Summary(4, 0, title: "A"), Summary(3, 0, title: "B")]);

        Assert.Equal(BenchmarkHostExit.NoSuccessfulBenchmark, exit.ExitCode);
        Assert.Contains("none of the 7 benchmark case(s)", exit.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SummaryWithoutCasesOrErrors_ExitsNonzero()
    {
        // BenchmarkDotNet's "no supported benchmark" summary: no report and no validation error.
        var exit = BenchmarkHostExit.Decide(runRequested: true, [Summary(cases: 0, successful: 0)]);

        Assert.Equal(BenchmarkHostExit.NoSuccessfulBenchmark, exit.ExitCode);
        Assert.NotNull(exit.Message);
    }

    [Theory]
    [InlineData(8, 7, 1)]
    [InlineData(8, 1, 7)]
    public void SomeCasesFailed_ExitsZeroWithAWarning(int cases, int successful, int failed)
    {
        var exit = BenchmarkHostExit.Decide(runRequested: true, [Summary(cases, successful)]);

        Assert.Equal(BenchmarkHostExit.Success, exit.ExitCode);
        Assert.Equal($"warning: {failed} of {cases} benchmark case(s) produced no successful report (NA).", exit.Message);
    }

    [Fact]
    public void OneSuccessfulSummary_BesideAFailedOne_ExitsZeroWithAWarning()
    {
        // The rule is "no benchmark case succeeded", counted over the whole invocation.
        var exit = BenchmarkHostExit.Decide(runRequested: true, [Summary(4, 0, title: "A"), Summary(2, 2, title: "B")]);

        Assert.Equal(BenchmarkHostExit.Success, exit.ExitCode);
        Assert.Equal("warning: 4 of 6 benchmark case(s) produced no successful report (NA).", exit.Message);
    }

    [Fact]
    public void CriticalValidationError_ExitsNonzeroAndNamesTheSummary()
    {
        var exit = BenchmarkHostExit.Decide(runRequested: true, [Summary(0, 0, critical: 2, title: "Broken")]);

        Assert.Equal(BenchmarkHostExit.NoSuccessfulBenchmark, exit.ExitCode);
        Assert.Equal("BenchmarkDotNet reported 2 critical validation error(s) (first in 'Broken').", exit.Message);
    }

    [Fact]
    public void CriticalValidationError_FailsEvenBesideASuccessfulSummary()
    {
        var exit = BenchmarkHostExit.Decide(
            runRequested: true,
            [Summary(3, 3, title: "Fine"), Summary(0, 0, critical: 1, title: "Broken"), Summary(0, 0, critical: 2, title: "Later")]);

        Assert.Equal(BenchmarkHostExit.NoSuccessfulBenchmark, exit.ExitCode);
        Assert.Equal("BenchmarkDotNet reported 3 critical validation error(s) (first in 'Broken').", exit.Message);
    }

    [Fact]
    public void NoSummary_ForARequestedRun_ExitsWithTheNothingRanCode()
    {
        // A filter or selection that matched nothing, or arguments BenchmarkDotNet rejected.
        var exit = BenchmarkHostExit.Decide(runRequested: true, []);

        Assert.Equal(BenchmarkHostExit.NoBenchmarkRun, exit.ExitCode);
        Assert.StartsWith("no benchmark was run (", exit.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void NoSummary_ForAnInformationalInvocation_ExitsZeroSilently()
    {
        // --help, --version, --info and --list print and return no summary by design.
        var exit = BenchmarkHostExit.Decide(runRequested: false, []);

        Assert.Equal(new BenchmarkHostExit(BenchmarkHostExit.Success, null), exit);
    }

    [Fact]
    public void InformationalFlag_NeverExcusesAFailedSummary()
    {
        // The flag only explains the absence of summaries; a summary that exists is judged by its content.
        Assert.Equal(
            BenchmarkHostExit.NoSuccessfulBenchmark,
            BenchmarkHostExit.Decide(runRequested: false, [Summary(2, 0)]).ExitCode);
        Assert.Equal(
            BenchmarkHostExit.NoSuccessfulBenchmark,
            BenchmarkHostExit.Decide(runRequested: false, [Summary(0, 0, critical: 1)]).ExitCode);
    }

    [Fact]
    public void EveryNonzeroExit_CarriesAReason()
    {
        BenchmarkSummaryOutcome[][] failures =
        [
            [],
            [Summary(0, 0)],
            [Summary(5, 0)],
            [Summary(5, 5), Summary(0, 0, critical: 1)],
        ];

        foreach (var summaries in failures)
        {
            var exit = BenchmarkHostExit.Decide(runRequested: true, summaries);
            Assert.NotEqual(BenchmarkHostExit.Success, exit.ExitCode);
            Assert.False(string.IsNullOrWhiteSpace(exit.Message));
        }
    }

    [Fact]
    public void NullSummaries_AreRejected()
        => Assert.Throws<ArgumentNullException>(() => BenchmarkHostExit.Decide(runRequested: true, null!));
}
