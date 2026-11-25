using System.Diagnostics;
using Xunit.Abstractions;

namespace KatLang.Tests.Infrastructure;

public class DagTraversalProbeTests
{
    [Theory]
    [InlineData(20)]
    [InlineData(40)]
    public void TheActualRowAndAssertions_RunOnTheCalibratedWorker(int depth)
    {
        var run = DagTraversalProbe.Run(typeof(Fixture), nameof(Fixture.Pass), depth, 2);
        Assert.Null(run.Failure);
        Assert.Contains($".{nameof(Fixture.Pass)}(depth={depth}) configuredStackBytes=1048576 pool=True queueMs=", run.Completion);
        Assert.Contains("completed=2 ", run.Completion);
    }

    [Theory]
    [InlineData(nameof(Fixture.AssertionFailure), 1, "Assert.Equal() Failure")]
    [InlineData(nameof(Fixture.NoGuard), 1, "did not execute its guarded body")]
    [InlineData(nameof(Fixture.WrongCount), 2, "Assert.Equal() Failure")]
    [InlineData(nameof(Fixture.FailureAfterCompletion), 1, "after completion")]
    public void MissingWorkWrongCountsAndOriginalFailures_CannotPass(string method, int count, string expected)
    {
        var run = DagTraversalProbe.Run(typeof(Fixture), method, null, count);
        Assert.NotNull(run.Failure);
        Assert.Contains(expected, run.Failure, StringComparison.Ordinal);
    }

    [Fact]
    public void AnAtomicTraversalThatNeverCompletes_IsTerminatedAndJoined()
    {
        var run = DagTraversalProbe.Run(typeof(Fixture), nameof(Fixture.Stuck), null, 1, TimeSpan.FromSeconds(3));
        Assert.NotNull(run.Failure);
        Assert.StartsWith("No work item", run.Failure, StringComparison.Ordinal);
        Assert.Contains("not a proven counterexample", run.Failure, StringComparison.Ordinal);
        var id = Assert.NotNull(run.ProcessId);
        try
        {
            using var child = Process.GetProcessById(id);
            Assert.True(child.HasExited);
        }
        catch (ArgumentException) { /* Already reaped. */ }
    }

    // Explicitly invoked methods; no xUnit attributes, so none is discovered as a separate test.
    public sealed class Fixture(ITestOutputHelper output)
    {
        public Task Pass(int depth)
            => DagTraversalProbe.Guard(GetType(), nameof(Pass), depth, 2, async () =>
            {
                Assert.True(Thread.CurrentThread.IsThreadPoolThread);
                Assert.True(depth is 20 or 40);
                DagTraversalProbe.Completed("assertions-before-suspension");
                await Task.Yield();
                Assert.True(Thread.CurrentThread.IsThreadPoolThread);
            }, output);

        public Task AssertionFailure()
            => DagTraversalProbe.Guard(GetType(), nameof(AssertionFailure), null, 1,
                () => { Assert.Equal(1, 2); return Task.CompletedTask; }, output);

        public Task NoGuard() => Task.CompletedTask;

        public Task WrongCount()
            => DagTraversalProbe.Guard(GetType(), nameof(WrongCount), null, 2, () => Task.CompletedTask, output);

        public async Task FailureAfterCompletion()
        {
            await DagTraversalProbe.Guard(GetType(), nameof(FailureAfterCompletion), null, 1, () => Task.CompletedTask, output);
            Assert.Fail("after completion");
        }

        public Task Stuck()
            => DagTraversalProbe.Guard(GetType(), nameof(Stuck), null, 1, () =>
            {
                while (true) Thread.Sleep(100);
            }, output);
    }
}
