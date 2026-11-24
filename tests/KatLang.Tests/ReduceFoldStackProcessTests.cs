using System.Diagnostics;
using KatLang.Evaluation;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// Long general <c>reduce</c> folds in a fresh child process (single-thread fold progress, November 2026;
/// <see cref="FoldTrampoline"/>), so a regression that overflows the host stack fails this test instead of killing
/// the test host. The child runs every fold on ONE 1 MiB thread — the stack of a browser worker — and requires the
/// issue's programs to complete there through both engine entry points, at lengths that nested steps could never
/// reach: a fold's chain keeps a bounded part of the host stack and continues on the heap, pumped on the calling
/// thread. Listed in the Release stack-suite job (<c>scripts/validate-stack-suites.ps1</c>): frame sizes depend on
/// the configuration.
/// </summary>
public sealed class ReduceFoldStackProcessTests
{
    private const string Child = "KATLANG_REDUCE_FOLD_STACK_CHILD";
    private const string Marker = "KATLANG_REDUCE_FOLD_STACK_MARKER";
    private const int OneMiB = 1024 * 1024;

    [Fact]
    public async Task LongGeneralFolds_CompleteOnOneMebibyteThread_InAChild()
    {
        var marker = Path.Combine(Path.GetTempPath(), $"katlang-reduce-fold-stack-{Guid.NewGuid():N}.txt");
        var start = SubprocessProbe.StartInfo(typeof(ReduceFoldStackProcessTests), nameof(ConstrainedChild));
        start.Environment[Child] = "1";
        start.Environment[Marker] = marker;
        try
        {
            using var process = Process.Start(start)!;
            var output = process.StandardOutput.ReadToEndAsync();
            var error = process.StandardError.ReadToEndAsync();
            await process.WaitForExitAsync();
            var text = await output + await error;
            Assert.True(process.ExitCode == 0, text);
            Assert.DoesNotContain("Stack overflow", text, StringComparison.OrdinalIgnoreCase);
            Assert.True(File.Exists(marker), text);
            Assert.Equal("reduce-fold-stack-ok", await File.ReadAllTextAsync(marker));
        }
        finally { File.Delete(marker); }
    }

    [Fact]
    public void ConstrainedChild()
    {
        if (Environment.GetEnvironmentVariable(Child) != "1") return;
        AstStructuralDepthProcessTests.RunOnThreadWithStack(OneMiB, () =>
        {
            var calling = Environment.CurrentManagedThreadId;
            var waits = FoldTrampoline.StalledPumps;

            // Program A through KatLangEngine.Run, program B through the Playground's RunAsync call shape.
            Success(KatLangEngine.Run("R(item, acc) = if(item > acc, item, acc)\nreduce(range(1, 100000), R, 0)"), "100000");
            Success(Playground("Step(x, (total, n)) = total + x, n + 1\nreduce(range(1, 100000), Step, (0, 0))"), "S[5000050000, 100000]");

            // A reducer that calls the host on both sides of its accumulator read: every call on this thread.
            var threads = new HashSet<int>();
            var operations = HostOperations.Create(HostOperation.Create("mark", (args, _) =>
            {
                threads.Add(Environment.CurrentManagedThreadId);
                return args[0];
            }, "x"));
            const string effectful = "R(item, acc) = mark(item) + acc + 0 * mark(0 - item)\nreduce(range(1, 20000), R, 0)";
            Success(KatLangEngine.Run(effectful, new RunOptions { HostOperations = operations }), "200010000");
            Assert.Equal([calling], threads);

            // A host that suppressed execution-context flow gets the fold completed, and its suppression back.
            Success(HostFlow.Under(Flow.Suppressed, () =>
            {
                var run = KatLangEngine.Run("Id(x) = x\nAdd(item, acc) = Id(item) + acc\nreduce(range(1, 20000), Add, 0)");
                Assert.True(ExecutionContext.IsFlowSuppressed());
                return run;
            }), "200010000");

            // Genuine recursion inside a step that runs on the heap keeps its ordinary checks: a structured
            // failure, never an overflow, as no twin hops off the pumping thread.
            var recursion = KatLangEngine.Run("Deep(n) = Deep(n + 1) + 1\nR(item, acc) = if(item == 1, Deep(0), acc + item)\nreduce(range(1, 20000), R, 0)");
            var failure = Assert.IsType<RunResult.EvalFailure>(recursion);
            Assert.Contains(failure.Errors, static error => error.Code is KatLangErrorCode.EvaluationDepthExceeded or KatLangErrorCode.EvaluationStackExhausted);

            Assert.Equal(waits, FoldTrampoline.StalledPumps);
            File.WriteAllText(Environment.GetEnvironmentVariable(Marker)!, "reduce-fold-stack-ok");
        });
    }

    // KatLangEngine.RunAsync as the Playground calls it, which completes inline for these programs.
    private static RunResult Playground(string source)
    {
        using var sourceCancellation = new CancellationTokenSource();
        using var evaluationCancellation = new CancellationTokenSource();
        var pending = KatLangEngine.RunAsync(source, new RunOptions
        {
            DownloadCode = static (_, _) => throw new InvalidOperationException("no module is loaded"),
            SourceProcessingCancellationToken = sourceCancellation.Token,
            EvaluationCancellationToken = evaluationCancellation.Token,
        });
        Assert.True(pending.IsCompleted, "RunAsync did not complete inline");
        return pending.GetAwaiter().GetResult();
    }

    private static void Success(RunResult result, string expected)
        => Assert.Equal(expected, SixRouteAgreement.Neutral(Assert.IsType<RunResult.Success>(result).Value));
}
