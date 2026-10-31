using System.Diagnostics;
using KatLang.ParserFuzz;

namespace KatLang.Tests.SemanticTesting;

/// <summary>
/// SEM-2B bounded supervision with deterministic worker fixtures. The worker is this repository-built
/// test assembly re-entered through <c>dotnet vstest</c> (the established child-process convention,
/// see <see cref="EvaluationLimitsProcessTests"/>): <see cref="Worker_Child"/> runs the SAME
/// <see cref="SemanticReplay.Work"/> the fuzz consumer's <c>semantic-worker</c> runs, or misbehaves on
/// purpose. Every fixture checks the reproducer is retained and the classification is its own:
/// completion, abnormal exit, malformed output, missing observation, and a timeout whose whole
/// worker tree is terminated and awaited.
/// </summary>
public class SemanticSupervisionTests
{
    private const string ModeVariable = "KATLANG_SEM2B_WORKER_MODE";
    private const string DescriptorVariable = "KATLANG_SEM2B_WORKER_DESCRIPTOR";
    private const string ResultVariable = "KATLANG_SEM2B_WORKER_RESULT";
    private const string PidVariable = "KATLANG_SEM2B_WORKER_PID_FILE";

    private sealed class Workspace : IDisposable
    {
        public Workspace(SemanticCase semanticCase)
        {
            Directory = System.IO.Directory.CreateTempSubdirectory("katlang-sem2b-supervision-");
            DescriptorPath = Path.Combine(Directory.FullName, "case.json");
            ResultPath = Path.Combine(Directory.FullName, "case.result.json");
            PidPath = Path.Combine(Directory.FullName, "worker.pid");
            File.WriteAllText(DescriptorPath, SemanticDescriptor.Write(semanticCase)); // persisted BEFORE dispatch
        }

        public DirectoryInfo Directory { get; }
        public string DescriptorPath { get; }
        public string ResultPath { get; }
        public string PidPath { get; }

        public SemanticWorkerCommand Command(string mode)
        {
            var arguments = new List<string>
            {
                "vstest",
                typeof(SemanticSupervisionTests).Assembly.Location,
                "--Tests:" + typeof(SemanticSupervisionTests).FullName + "." + nameof(Worker_Child),
            };
            if (mode == "long-output") arguments.Add("--logger:console;verbosity=detailed");
            var environment = new Dictionary<string, string>
            {
                [ModeVariable] = mode,
                [DescriptorVariable] = DescriptorPath,
                [ResultVariable] = ResultPath,
                [PidVariable] = PidPath,
                ["DOTNET_NOLOGO"] = "1",
            };
            return new SemanticWorkerCommand("dotnet", arguments, environment, DescriptorPath, ResultPath);
        }

        public void Dispose()
        {
            try { Directory.Delete(recursive: true); }
            catch (IOException) { /* best effort */ }
        }
    }

    private static SemanticCase Case => SemanticGrammarCorpusTests.Cases.First(c => c.Kind == SemanticCaseKind.ValidSuccess
        && c.Tier == "seeded" && c.Paths != SemanticPath.None && c.Members.Length > 1);

    private static readonly TimeSpan Generous = TimeSpan.FromSeconds(120);

    [Fact]
    public void NormalCompletion_ReturnsTheWorkersSemanticVerdict()
    {
        using var workspace = new Workspace(Case);
        var run = SemanticSupervisor.Run(workspace.Command("normal"), Generous);
        Assert.True(run.Verdict == SemanticVerdict.Passed, run.Describe() + Environment.NewLine + run.Stdout + run.Stderr);
        Assert.Equal(0, run.ExitCode);
        Assert.Equal(Case.CaseId, run.Result!.CaseId);
        Assert.True(File.Exists(workspace.DescriptorPath));
    }

    [Fact]
    public void AbnormalExit_IsACrash_AndTheReproducerIsRetained()
    {
        using var workspace = new Workspace(Case);
        var run = SemanticSupervisor.Run(workspace.Command("exit"), Generous);
        Assert.Equal(SemanticVerdict.Crash, run.Verdict);
        Assert.NotEqual(0, run.ExitCode);
        Assert.Null(run.Result);
        Assert.True(File.Exists(run.DescriptorPath));
        Assert.True(run.Stdout.Length <= SemanticSupervisor.MaxCapturedChars + 16 && run.Stderr.Length <= SemanticSupervisor.MaxCapturedChars + 16);
    }

    [Fact]
    public void MalformedOrIncompleteOutput_HasItsOwnClassification()
    {
        using (var workspace = new Workspace(Case))
        {
            var malformed = SemanticSupervisor.Run(workspace.Command("malformed"), Generous);
            Assert.Equal(SemanticVerdict.MalformedOutput, malformed.Verdict);
        }

        using (var workspace = new Workspace(Case))
        {
            var missing = SemanticSupervisor.Run(workspace.Command("missing"), Generous);
            Assert.Equal(SemanticVerdict.MissingObservation, missing.Verdict);
            Assert.Contains("no observation for", missing.Detail, StringComparison.Ordinal);
        }

        foreach (var mode in new[] { "empty", "missing-transform", "wrong-case", "missing-data", "missing-path" })
        {
            using var workspace = new Workspace(Case);
            var run = SemanticSupervisor.Run(workspace.Command(mode), Generous);
            Assert.Equal(mode is "empty" or "missing-transform" or "missing-path" ? SemanticVerdict.MissingObservation : SemanticVerdict.MalformedOutput, run.Verdict);
        }
    }

    [Fact]
    public void UnbrokenOutput_IsBoundedAndDrained_AndSupervisionEvidenceIsRetained()
    {
        using var workspace = new Workspace(Case);
        var run = SemanticSupervisor.Run(workspace.Command("long-output"), Generous);
        Assert.True(run.Verdict == SemanticVerdict.Passed, run.Describe() + run.Stderr);
        Assert.True(run.Stdout.Length <= SemanticSupervisor.MaxCapturedChars + 16);
        Assert.Contains("[truncated]", run.Stdout, StringComparison.Ordinal);
        var evidence = File.ReadAllText(workspace.ResultPath + ".supervision.txt");
        Assert.Contains("ExitCode", evidence, StringComparison.Ordinal);
        Assert.Contains("Profiles", evidence, StringComparison.Ordinal);
        Assert.Contains("Stdout", evidence, StringComparison.Ordinal);
    }

    [Fact]
    public async Task ExternalCancellation_TerminatesAnAlreadyRunningWorker()
    {
        using var workspace = new Workspace(Case);
        using var cancellation = new CancellationTokenSource();
        using var watchdog = new CancellationTokenSource(Generous);
        var pending = Task.Run(() => SemanticSupervisor.Run(workspace.Command("hang"), Generous, cancellation.Token));
        var pid = 0;
        try
        {
            while (!File.Exists(workspace.PidPath)
                   || !int.TryParse(await File.ReadAllTextAsync(workspace.PidPath, watchdog.Token), out pid))
                await Task.Delay(50, watchdog.Token);
        }
        catch
        {
            cancellation.Cancel();
            await pending;
            throw;
        }
        finally
        {
            cancellation.Cancel();
        }
        var run = await pending;
        Assert.Equal(SemanticVerdict.SupervisorCancellation, run.Verdict);
        Assert.True(Exited(pid));
        Assert.True(File.Exists(run.DescriptorPath));
    }

    /// <summary>
    /// The external deadline terminates the whole worker tree, AWAITS it, keeps the reproducer, and
    /// reports a timeout — never a semantic result, never a language-level cancellation.
    /// </summary>
    [Fact]
    public void Timeout_TerminatesTheWorkerTree_AndKeepsTheReproducer()
    {
        // The worker's pid file is its readiness signal, so the 3-second workload deadline starts
        // only once the (possibly slow, loaded) test host has reached the hanging fixture.
        using var workspace = new Workspace(Case);
        var run = SemanticSupervisor.Run(workspace.Command("hang") with { ReadyPath = workspace.PidPath }, TimeSpan.FromSeconds(3));
        Assert.True(run.Verdict == SemanticVerdict.Timeout, run.Describe());
        Assert.Contains("deadline", run.Detail, StringComparison.Ordinal);
        Assert.Null(run.ExitCode);
        Assert.Null(run.Result);
        Assert.True(File.Exists(run.DescriptorPath));

        // The worker (the test host under vstest) recorded its pid before hanging; it must be gone.
        var pid = int.Parse(File.ReadAllText(workspace.PidPath).Trim(), System.Globalization.CultureInfo.InvariantCulture);
        Assert.True(Exited(pid), $"worker process {pid} survived its supervisor");
    }

    /// <summary>A worker that never becomes ready is bounded too, and is also a timeout.</summary>
    [Fact]
    public void StartupBound_TerminatesAWorkerThatNeverBecomesReady()
    {
        using var workspace = new Workspace(Case);
        var never = Path.Combine(workspace.Directory.FullName, "never-written");
        var command = workspace.Command("hang") with { ReadyPath = never, StartupDeadline = TimeSpan.FromSeconds(1) };
        var run = SemanticSupervisor.Run(command, Generous);
        Assert.True(run.Verdict == SemanticVerdict.Timeout, run.Describe());
        Assert.Contains("not ready", run.Detail, StringComparison.Ordinal);
        Assert.True(File.Exists(run.DescriptorPath));
    }

    private static bool Exited(int pid)
    {
        // Kill(entireProcessTree) is awaited for the root; give the OS a bounded moment for the leaf.
        for (var attempt = 0; attempt < 50; attempt++)
        {
            try
            {
                using var process = Process.GetProcessById(pid);
                if (process.HasExited) return true;
            }
            catch (ArgumentException)
            {
                return true;
            }

            Thread.Sleep(100);
        }

        return false;
    }

    /// <summary>The child half. Inert (returns immediately) unless launched by a fixture above.</summary>
    [Fact]
    public void Worker_Child()
    {
        var mode = Environment.GetEnvironmentVariable(ModeVariable);
        if (string.IsNullOrEmpty(mode)) return;

        var descriptor = Environment.GetEnvironmentVariable(DescriptorVariable)!;
        var result = Environment.GetEnvironmentVariable(ResultVariable)!;
        var pidPath = Environment.GetEnvironmentVariable(PidVariable)!;
        var pendingPidPath = pidPath + ".pending";
        // Publish readiness only after the writer closes, so a parent observing the signal
        // can read the complete PID without racing an open write handle.
        File.WriteAllText(pendingPidPath, Environment.ProcessId.ToString(System.Globalization.CultureInfo.InvariantCulture));
        File.Move(pendingPidPath, pidPath);
        switch (mode)
        {
            case "normal":
                Assert.Equal(0, SemanticReplay.Work(descriptor, result, SemanticReplay.Mode.Recipe));
                return;
            case "long-output":
                Console.Write(new string('x', SemanticSupervisor.MaxCapturedChars * 16));
                Assert.Equal(0, SemanticReplay.Work(descriptor, result, SemanticReplay.Mode.Recipe));
                return;
            case "empty":
                return;
            case "wrong-case":
            case "missing-transform":
            case "missing-path":
                var observed = SemanticRunner.Run(Case);
                observed = mode == "wrong-case" ? observed with { CaseId = "another-case" }
                    : mode == "missing-path" ? observed with { PathsExercised = SemanticPath.None }
                    : observed with { Runs = [.. observed.Runs.Where(r => r.Member == SemanticMember.BaseRole)] };
                File.WriteAllText(result, SemanticDescriptor.WriteResultDocument(observed));
                return;
            case "missing-data":
                var missingData = System.Text.Json.Nodes.JsonNode.Parse(SemanticDescriptor.WriteResultDocument(SemanticRunner.Run(Case)))!;
                foreach (var observation in missingData["result"]!["observations"]!.AsArray())
                    observation!["valueIdentity"] = null;
                File.WriteAllText(result, missingData.ToJsonString());
                return;
            case "exit":
                Environment.Exit(7);
                return;
            case "malformed":
                File.WriteAllText(result, "{ this is not a result document");
                return;
            case "missing":
                // A well-formed result that observed nothing: never evidence of a pass.
                File.WriteAllText(result, SemanticDescriptor.WriteResultDocument(
                    new SemanticCaseResult(Case.CaseId, SemanticVerdict.Passed, [], [], SemanticPath.None, [], [])));
                return;
            case "hang":
                Thread.Sleep(Timeout.Infinite);
                return;
            default:
                throw new InvalidOperationException("unknown worker fixture mode " + mode);
        }
    }
}
