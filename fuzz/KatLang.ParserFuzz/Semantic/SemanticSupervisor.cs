using System.Diagnostics;
using System.Globalization;
using System.Reflection;
using System.Text;
using System.Text.Json;

namespace KatLang.ParserFuzz;

/// <summary>
/// A worker launch: a known, repository-built executable with STRUCTURED arguments (an argument
/// list, never a shell string), extra environment, and the result file it must write.
/// </summary>
internal sealed record SemanticWorkerCommand(
    string FileName,
    IReadOnlyList<string> Arguments,
    IReadOnlyDictionary<string, string> Environment,
    string DescriptorPath,
    string ResultPath)
{
    /// <summary>
    /// Optional readiness file the worker writes just before it starts the workload. When set, the
    /// workload deadline counts from readiness, so a slow host start (a test host discovering a large
    /// assembly under load) cannot consume it; <see cref="StartupDeadline"/> bounds the time before
    /// readiness separately, and its expiry is also a <see cref="SemanticVerdict.Timeout"/>.
    /// </summary>
    public string? ReadyPath { get; init; }

    public TimeSpan StartupDeadline { get; init; } = TimeSpan.FromMinutes(5);
}

/// <summary>What one supervised execution produced. A timeout or a crash is never a semantic comparison.</summary>
internal sealed record SemanticSupervisedRun(
    SemanticVerdict Verdict,
    int? ExitCode,
    TimeSpan Elapsed,
    string Stdout,
    string Stderr,
    string DescriptorPath,
    SemanticDescriptor.ResultSummary? Result,
    string Detail)
{
    public string Describe()
        => string.Create(CultureInfo.InvariantCulture,
            $"{Verdict} exit={ExitCode?.ToString(CultureInfo.InvariantCulture) ?? "-"} elapsed={Elapsed.TotalSeconds:F1}s {Detail}");
}

/// <summary>
/// Bounded child-process supervision for generated workloads that could hang or terminate the
/// host (SEM-2B). One worker at a time — no fan-out. The supervisor:
/// <list type="bullet">
/// <item>starts the worker with redirected, BOUNDED stdout/stderr capture;</item>
/// <item>applies an external wall-clock deadline on top of the engine's own limits;</item>
/// <item>on expiry kills the whole process tree and AWAITS its exit before returning;</item>
/// <item>retains the descriptor path, exit status and captured output;</item>
/// <item>classifies timeout, crash/abnormal exit, malformed result, missing observation, semantic
/// mismatch and harness failure separately.</item>
/// </list>
/// The descriptor is always persisted by the caller BEFORE dispatch, so a crash or hang leaves the
/// reproducer behind. A supervising timeout is never converted into a language cancellation.
/// </summary>
internal static class SemanticSupervisor
{
    internal static readonly TimeSpan DefaultDeadline = TimeSpan.FromSeconds(60);

    internal const int MaxCapturedChars = 16 * 1024;

    /// <summary>
    /// The fuzz consumer relaunching itself as <c>semantic-worker</c>. The result document goes to
    /// <paramref name="resultPath"/> — a campaign's own output directory or a temporary location,
    /// never beside a checked-in descriptor.
    /// </summary>
    internal static SemanticWorkerCommand SelfWorker(string descriptorPath, string resultPath, SemanticReplay.Mode mode)
    {
        var host = System.Environment.ProcessPath ?? throw new InvalidOperationException("no process path");
        var entry = Assembly.GetEntryAssembly();
        var selfContained = entry is not null
            && string.Equals(Path.GetFileNameWithoutExtension(host), entry.GetName().Name, StringComparison.OrdinalIgnoreCase);
        var arguments = new List<string>();
        if (!selfContained && entry?.Location is { Length: > 0 } dll) arguments.Add(dll);
        arguments.AddRange(["semantic-worker", descriptorPath, resultPath]);
        if (mode == SemanticReplay.Mode.ExactSource) arguments.Add("--exact-source");
        return new SemanticWorkerCommand(host, arguments, new Dictionary<string, string>(), descriptorPath, resultPath);
    }

    internal static SemanticSupervisedRun Run(SemanticWorkerCommand command, TimeSpan deadline, CancellationToken cancellationToken = default)
    {
        ArgumentNullException.ThrowIfNull(command);
        if (!SemanticDescriptor.TryParse(SemanticReplay.ReadBounded(command.DescriptorPath), out var descriptor, out var descriptorProblem))
            return new SemanticSupervisedRun(SemanticVerdict.HarnessFailure, null, TimeSpan.Zero, "", "",
                command.DescriptorPath, null, "descriptor rejected before dispatch: " + descriptorProblem);
        File.Delete(command.ResultPath); // a stale result must never masquerade as the worker's output
        if (command.ReadyPath is { } staleReady) TryDelete(staleReady);

        var startInfo = new ProcessStartInfo(command.FileName)
        {
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            RedirectStandardInput = true,
            UseShellExecute = false,
            CreateNoWindow = true,
        };
        foreach (var argument in command.Arguments) startInfo.ArgumentList.Add(argument);
        foreach (var (key, value) in command.Environment) startInfo.Environment[key] = value;
        foreach (var key in startInfo.Environment.Keys.Where(k => k.StartsWith("KATLANG_REGENERATE_", StringComparison.OrdinalIgnoreCase)).ToList())
            startInfo.Environment.Remove(key);

        var clock = Stopwatch.StartNew();
        using var process = new Process { StartInfo = startInfo };
        var stdout = new BoundedText(MaxCapturedChars);
        var stderr = new BoundedText(MaxCapturedChars);
        SemanticSupervisedRun Finish(SemanticSupervisedRun run)
        {
            File.WriteAllText(command.ResultPath + ".supervision.txt", JsonSerializer.Serialize(new
            {
                run.Verdict, run.ExitCode, run.Elapsed, run.DescriptorPath, run.Detail, run.Stdout, run.Stderr,
                Profiles = descriptor.Case.Profiles,
            },
                new JsonSerializerOptions { WriteIndented = true }));
            return run;
        }

        if (cancellationToken.IsCancellationRequested)
            return Finish(new SemanticSupervisedRun(SemanticVerdict.SupervisorCancellation, null, clock.Elapsed, "", "",
                command.DescriptorPath, null, "supervisor cancelled before dispatch"));

        try
        {
            process.Start();
        }
        catch (Exception exception) when (exception is System.ComponentModel.Win32Exception or InvalidOperationException)
        {
            return Finish(new SemanticSupervisedRun(SemanticVerdict.HarnessFailure, null, clock.Elapsed, "", exception.Message,
                command.DescriptorPath, null, "worker could not be started"));
        }

        process.StandardInput.Close();
        // Read fixed-size chunks: ReadLine/DataReceived can buffer an unbounded single line before
        // our capture limit ever sees it. Continue draining after truncation to avoid pipe deadlock.
        var output = Task.WhenAll(ReadOutput(process.StandardOutput, stdout), ReadOutput(process.StandardError, stderr));

        SemanticSupervisedRun Stop(SemanticVerdict verdict, string detail)
        {
            Terminate(process);
            output.Wait(TimeSpan.FromSeconds(5));
            return Finish(new SemanticSupervisedRun(verdict, null, clock.Elapsed, stdout.Text, stderr.Text,
                command.DescriptorPath, null, detail));
        }

        if (command.ReadyPath is { } ready)
        {
            // The startup bound: wait for readiness, the worker's exit, or the bound — whichever first.
            var startup = Stopwatch.StartNew();
            while (!File.Exists(ready) && !process.WaitForExit(TimeSpan.FromMilliseconds(50)))
            {
                if (cancellationToken.IsCancellationRequested)
                    return Stop(SemanticVerdict.SupervisorCancellation, "supervisor cancelled; worker tree terminated");
                if (startup.Elapsed > command.StartupDeadline)
                {
                    return Stop(SemanticVerdict.Timeout,
                        $"worker not ready within {command.StartupDeadline.TotalSeconds.ToString(CultureInfo.InvariantCulture)}s; worker tree terminated");
                }
            }
        }

        using var deadlineCancellation = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
        deadlineCancellation.CancelAfter(deadline);
        try
        {
            process.WaitForExitAsync(deadlineCancellation.Token).GetAwaiter().GetResult();
            output.WaitAsync(deadlineCancellation.Token).GetAwaiter().GetResult();
        }
        catch (OperationCanceledException)
        {
            return cancellationToken.IsCancellationRequested
                ? Stop(SemanticVerdict.SupervisorCancellation, "supervisor cancelled; worker tree terminated")
                : Stop(SemanticVerdict.Timeout, $"deadline {deadline.TotalSeconds.ToString(CultureInfo.InvariantCulture)}s expired; worker tree terminated");
        }

        var exitCode = process.ExitCode;
        if (!File.Exists(command.ResultPath))
        {
            return Finish(new SemanticSupervisedRun(exitCode == 0 ? SemanticVerdict.MissingObservation : SemanticVerdict.Crash,
                exitCode, clock.Elapsed, stdout.Text, stderr.Text,
                command.DescriptorPath, null, $"worker exited with {exitCode.ToString(CultureInfo.InvariantCulture)} and wrote no result"));
        }

        string text;
        try
        {
            text = SemanticReplay.ReadBounded(command.ResultPath);
        }
        catch (Exception exception) when (exception is IOException or InvalidDataException)
        {
            return Finish(new SemanticSupervisedRun(SemanticVerdict.MalformedOutput, exitCode, clock.Elapsed, stdout.Text, stderr.Text,
                command.DescriptorPath, null, exception.Message));
        }

        if (!SemanticDescriptor.TryParseResult(text, out var summary, out var problem))
        {
            return Finish(new SemanticSupervisedRun(SemanticVerdict.MalformedOutput, exitCode, clock.Elapsed, stdout.Text, stderr.Text,
                command.DescriptorPath, null, problem));
        }

        if (exitCode != 0)
        {
            return Finish(new SemanticSupervisedRun(SemanticVerdict.Crash, exitCode, clock.Elapsed, stdout.Text, stderr.Text,
                command.DescriptorPath, summary, $"worker wrote a result but exited with {exitCode.ToString(CultureInfo.InvariantCulture)}"));
        }

        if (summary.CaseId != descriptor.Case.CaseId)
            return Finish(new SemanticSupervisedRun(SemanticVerdict.MalformedOutput, exitCode, clock.Elapsed, stdout.Text, stderr.Text,
                command.DescriptorPath, summary, "worker result belongs to a different case"));

        // Every profile the recorded case requires must appear in the worker's observations.
        if (summary.Verdict != SemanticVerdict.RecipeDrift)
        {
            var required = descriptor.Case.Profiles.Select(p => p + "/" + SemanticMember.BaseRole)
                .Concat(descriptor.Case.Members.Skip(1).Select(m => SemanticProfiles.SyncOptimized + "/" + m.Role));
            var missing = required.Where(p => !summary.ObservedProfiles.Contains(p, StringComparer.Ordinal))
                .ToList();
            if (missing.Count > 0)
            {
                return Finish(new SemanticSupervisedRun(SemanticVerdict.MissingObservation, exitCode, clock.Elapsed, stdout.Text, stderr.Text,
                    command.DescriptorPath, summary, "no observation for " + string.Join(", ", missing)));
            }
        }

        if (summary.Verdict == SemanticVerdict.Passed
            && (descriptor.Case.Paths & ~summary.CoverageResult.PathsExercised) != SemanticPath.None)
            return Finish(new SemanticSupervisedRun(SemanticVerdict.MissingObservation, exitCode, clock.Elapsed, stdout.Text, stderr.Text,
                command.DescriptorPath, summary, "worker did not admit every required path"));

        return Finish(new SemanticSupervisedRun(summary.Verdict, exitCode, clock.Elapsed, stdout.Text, stderr.Text,
            command.DescriptorPath, summary, summary.Findings.IsEmpty ? summary.CaseId : summary.Findings[0]));
    }

    private static async Task ReadOutput(StreamReader reader, BoundedText capture)
    {
        var buffer = new char[4096];
        int count;
        while ((count = await reader.ReadAsync(buffer).ConfigureAwait(false)) != 0)
            capture.Append(buffer.AsSpan(0, count));
    }

    /// <summary>Kills the whole worker tree and awaits the root's exit: cleanup is awaited, never assumed.</summary>
    private static void Terminate(Process process)
    {
        try { process.Kill(entireProcessTree: true); }
        catch (InvalidOperationException) { /* exited between the check and the kill */ }
        process.WaitForExit();
    }

    private static void TryDelete(string path)
    {
        try { File.Delete(path); }
        catch (IOException) { /* best effort; a stale file would be overwritten atomically */ }
    }

    /// <summary>Thread-safe capture that keeps at most <c>limit</c> characters and marks truncation.</summary>
    private sealed class BoundedText(int limit)
    {
        private readonly StringBuilder _text = new();
        private bool _truncated;

        public void Append(ReadOnlySpan<char> chunk)
        {
            lock (_text)
            {
                var count = Math.Min(chunk.Length, limit - _text.Length);
                _text.Append(chunk[..count]);
                _truncated |= count < chunk.Length;
            }
        }

        public string Text
        {
            get
            {
                lock (_text) return _truncated ? _text + "…[truncated]" : _text.ToString();
            }
        }
    }
}
