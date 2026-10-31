using System.Diagnostics;

namespace KatLang.Tests.Infrastructure;

/// <summary>
/// The termination-probe harness used by the parser termination sweeps: the stall window resets
/// only on completed work, and success, failure, stall, missing or duplicate completion and
/// malformed records stay distinguishable. Window rules are checked with synthetic times; child
/// processes are used only where the outcome does not depend on timing.
/// </summary>
public class TerminationProbeTests
{
    private const string Probe = "Some.Probe.Sweep";
    private static readonly TimeSpan Window = TimeSpan.FromSeconds(2);

    private static long At(double seconds) => 1_000_000 + (long)(seconds * Stopwatch.Frequency);

    private static string Progress(long completed, long started, string phase = "original", string input = "x", double completedAt = 1)
        => $"{TerminationProbe.ProgressPrefix}completed={completed} completedAt={(completed == 0 ? 0 : At(completedAt))} started={started} phase={phase} input={input}";

    private static TerminationMonitor Monitor() => new(Probe, At(0), Window);

    private static string? Verdict(TerminationMonitor monitor, IEnumerable<string> lines, long expected = 2, int exitCode = 0)
    {
        foreach (var line in lines)
            monitor.Observe(line, At(1));
        return monitor.Evaluate(exitCode, stalled: false, expected, "", At(2)).Failure;
    }

    private static IEnumerable<string> Successful(long completed = 2)
        => ["PROBE START " + Probe, Progress(completed, completed), $"{TerminationProbe.CompletePrefix}completed={completed} extra=1", "PROBE PASS " + Probe];

    [Fact]
    public void AWorkerThatKeepsCompleting_OutlivesTheWindow_WithoutStalling()
    {
        var monitor = Monitor();
        for (var second = 1; second <= 10; second++)
        {
            monitor.Observe(Progress(second, second, completedAt: second), At(second));
            Assert.False(monitor.IsStalled(At(second + 0.9)));
        }
        Assert.Equal(10, monitor.Completed);
    }

    [Fact]
    public void HeartbeatsPhaseChangesStartsAndRepeatedOrdinals_NeverResetTheWindow()
    {
        var monitor = Monitor();
        monitor.Observe(Progress(1, 1), At(1));
        monitor.Observe(Progress(1, 2, "original", "next"), At(1.5));
        monitor.Observe(Progress(1, 2, "suffix-recovery", "next"), At(2));
        monitor.Observe($"{TerminationProbe.HeartbeatPrefix}completed=1", At(2.5));
        monitor.Observe(Progress(1, 2, "suffix-recovery", "next"), At(2.9));
        monitor.Observe("PROBE START " + Probe, At(2.95));
        Assert.False(monitor.IsStalled(At(2.99)));
        Assert.True(monitor.IsStalled(At(3.01)));
    }

    [Fact]
    public void StartUp_CountsAgainstTheWindow_UntilTheFirstCompletion()
    {
        var monitor = Monitor();
        monitor.Observe("PROBE START " + Probe, At(1));
        monitor.Observe(Progress(0, 1), At(1.5));
        Assert.True(monitor.IsStalled(At(2.01)));
    }

    [Fact]
    public void DelayedProgressRecords_CannotMaskAChildThatStoppedCompletingWork()
    {
        var monitor = Monitor();
        // A pipe backlog is drained much later than the work described in it.
        monitor.Observe(Progress(1, 1, completedAt: 1), At(10));
        monitor.Observe(Progress(2, 3, completedAt: 2), At(11));
        Assert.Equal(2, monitor.Completed);
        Assert.True(monitor.IsStalled(At(11.01)));
    }

    [Fact]
    public void FutureReversedOrRewrittenCompletionTimestamps_AreProtocolErrors()
    {
        foreach (var record in new[]
        {
            Progress(2, 2, completedAt: 3), // In the future when observed at second 1.
            Progress(2, 2, completedAt: 0.5), // New work with an older completion time.
            Progress(1, 2, completedAt: 0.5), // Same work with a rewritten time.
        })
        {
            var monitor = Monitor();
            monitor.Observe(Progress(1, 1), At(1));
            var failure = Verdict(monitor, Successful().Prepend(record));
            Assert.NotNull(failure);
            Assert.Contains("timestamp", failure, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void ACompleteWellFormedRun_Passes()
        => Assert.Null(Verdict(Monitor(), Successful()));

    [Theory]
    [InlineData("TERMINATION PROGRESS completed=x started=1 phase=original input=a", "malformed progress record")]
    [InlineData("TERMINATION PROGRESS completed=1 started=1 phase= input=a", "malformed progress record")]
    [InlineData("TERMINATION PROGRESS completed=1 started=1 phase=original", "malformed progress record")]
    [InlineData("TERMINATION PROGRESS completed=2 completedAt=1000000 started=4 phase=original input=a", "neither the completed nor the next")]
    [InlineData("TERMINATION PROGRESS completed=0 completedAt=0 started=0 phase=original input=a", "went back")]
    [InlineData("TERMINATION HEARTBEAT completed=", "malformed heartbeat")]
    [InlineData("TERMINATION HEARTBEAT completed=1", "a heartbeat reported 1")]
    public void MalformedOrInconsistentRecords_FailAnOtherwiseSuccessfulRun(string record, string expected)
    {
        var monitor = Monitor();
        monitor.Observe(Progress(2, 2), At(1));
        var failure = Verdict(monitor, Successful().Prepend(record));
        Assert.NotNull(failure);
        Assert.Contains(expected, failure, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingDuplicateOrMiscountedCompletion_IsNeverAPass()
    {
        Assert.Contains("saw 0", Verdict(Monitor(), Successful().Where(l => !l.StartsWith(TerminationProbe.CompletePrefix, StringComparison.Ordinal))));
        Assert.Contains("saw 2", Verdict(Monitor(), Successful().Append($"{TerminationProbe.CompletePrefix}completed=2")));
        Assert.Contains("does not report 3", Verdict(Monitor(), Successful(), expected: 3));
        Assert.Contains("one PROBE START and one PROBE PASS", Verdict(Monitor(), Successful().Where(l => !l.StartsWith("PROBE PASS", StringComparison.Ordinal))));
    }

    [Fact]
    public void AFailingExit_IsAFailureEvenAfterACompletionRecord()
        => Assert.Contains("exit code 1", Verdict(Monitor(), Successful(), exitCode: 1));

    [Fact]
    public void ACompletedChild_PassesWithItsCompletionRecord()
    {
        var run = TerminationProbe.Run(typeof(Fixture), nameof(Fixture.Pass), 3, TerminationProbe.ParserStallWindow);
        Assert.Null(run.Failure);
        Assert.Equal($"{TerminationProbe.CompletePrefix}completed=3 fixture=pass", run.Completion);
    }

    [Fact]
    public void AnAssertionFailure_StaysAFailure_WithItsInputAndPhase()
    {
        var run = TerminationProbe.Run(typeof(Fixture), nameof(Fixture.FailInSuffix), 3, TerminationProbe.ParserStallWindow);
        Assert.NotNull(run.Failure);
        Assert.Contains("exit code 1", run.Failure, StringComparison.Ordinal);
        Assert.Contains($"{TerminationProbe.FailedPrefix}input #2 during the suffix-recovery phase: bad\\ninput", run.Failure, StringComparison.Ordinal);
        Assert.Contains("fixture assertion failed", run.Failure, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(nameof(Fixture.MissingCompletion), "saw 0")]
    [InlineData(nameof(Fixture.DuplicateCompletion), "saw 2")]
    [InlineData(nameof(Fixture.MalformedRecord), "malformed progress record")]
    [InlineData(nameof(Fixture.CompletionThenFailure), "exit code 1")]
    public void AChildThatBreaksTheProtocol_Fails(string method, string expected)
    {
        var run = TerminationProbe.Run(typeof(Fixture), method, 3, TerminationProbe.ParserStallWindow);
        Assert.NotNull(run.Failure);
        Assert.Contains(expected, run.Failure, StringComparison.Ordinal);
    }

    /// <summary>
    /// A child that never completes its second item while its reporter keeps emitting status
    /// changes and heartbeats is terminated once the (deliberately short) window passes. The
    /// outcome does not depend on timing: the fixture never completes again, so the only possible
    /// verdict is a stall.
    /// </summary>
    [Fact]
    public void AStuckChildEmittingHeartbeatsAndStatus_IsTerminatedAndJoined()
    {
        var run = TerminationProbe.Run(typeof(Fixture), nameof(Fixture.StuckWithNoise), 3, TimeSpan.FromSeconds(3));
        Assert.NotNull(run.Failure);
        Assert.StartsWith($"No work item of {typeof(Fixture).FullName}.{nameof(Fixture.StuckWithNoise)} completed for 3 s", run.Failure, StringComparison.Ordinal);
        Assert.Contains("not a proven counterexample", run.Failure, StringComparison.Ordinal);
        var id = Assert.NotNull(run.ProcessId);
        try
        {
            using var child = Process.GetProcessById(id);
            Assert.True(child.HasExited);
        }
        catch (ArgumentException)
        {
            // Gone.
        }
    }

    // These are explicitly named probes, not independently discovered tests.
    public sealed class Fixture
    {
        public void Pass()
        {
            using var progress = TerminationProgress.Start();
            for (var item = 1; item <= 3; item++)
            {
                progress.Begin(item, "original", $"input{item}");
                progress.Complete();
            }
            progress.Finish("fixture=pass");
        }

        public void FailInSuffix()
        {
            using var progress = TerminationProgress.Start();
            progress.Begin(1, "original", "good");
            progress.Complete();
            progress.Begin(2, "original", "bad\ninput");
            try
            {
                progress.Enter("suffix-recovery");
                Assert.Fail("fixture assertion failed");
            }
            catch (Exception) when (progress.ReportFailure())
            {
                throw;
            }
        }

        public void MissingCompletion()
        {
            using var progress = TerminationProgress.Start();
            for (var item = 1; item <= 3; item++)
            {
                progress.Begin(item, "original", "x");
                progress.Complete();
            }
        }

        public void DuplicateCompletion()
        {
            Pass();
            Console.WriteLine($"{TerminationProbe.CompletePrefix}completed=3 fixture=pass");
        }

        public void MalformedRecord()
        {
            Console.WriteLine($"{TerminationProbe.ProgressPrefix}completed=x");
            Pass();
        }

        public void CompletionThenFailure()
        {
            Pass();
            throw new InvalidOperationException("failed after its completion record");
        }

        public void StuckWithNoise()
        {
            using var progress = TerminationProgress.Start();
            progress.Begin(1, "original", "first");
            progress.Complete();
            progress.Begin(2, "original", "stuck");
            while (true)
            {
                progress.Enter("phase-a");
                Thread.Sleep(600);
                progress.Enter("phase-b");
                Thread.Sleep(1500); // quiet long enough for heartbeats
            }
        }
    }
}
