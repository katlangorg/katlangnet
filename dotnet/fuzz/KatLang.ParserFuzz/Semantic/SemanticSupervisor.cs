using System.Collections.Immutable;
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

/// <summary>
/// A batch worker launch (exhaustive campaigns): a known, repository-built executable with
/// structured arguments and extra environment, and the manifest of descriptor/result pairs it
/// replays in order.
/// </summary>
internal sealed record SemanticBatchWorkerCommand(
    string FileName,
    IReadOnlyList<string> Arguments,
    IReadOnlyDictionary<string, string> Environment,
    string ManifestPath)
{
    /// <summary>
    /// Optional readiness file the batch worker writes just before it replays its first member, as for
    /// a single worker (<see cref="SemanticWorkerCommand.ReadyPath"/>). When set, the progress deadline
    /// starts at readiness, so a slow host start (a test host discovering a large assembly under load)
    /// cannot consume the first member's deadline; <see cref="StartupDeadline"/> bounds the time before
    /// readiness separately, and its expiry is also a <see cref="SemanticVerdict.Timeout"/>.
    /// </summary>
    public string? ReadyPath { get; init; }

    public TimeSpan StartupDeadline { get; init; } = TimeSpan.FromMinutes(5);
}

/// <summary>
/// One member of a supervised batch: the persisted case, where its descriptor and result live, and —
/// once its result was judged — the verdict, the result summary and the detail. A member without a
/// verdict wrote no result: it was in flight when the child ended, or was never reached.
/// </summary>
internal sealed record SemanticBatchMember(
    SemanticCase Case,
    string DescriptorPath,
    string ResultPath,
    SemanticVerdict? Verdict = null,
    SemanticDescriptor.ResultSummary? Summary = null,
    string Detail = "");

/// <summary>
/// What one supervised batch child did: <see cref="ChildFailure"/> is <c>null</c> after a clean exit,
/// else how the child ended (timeout, crash, harness failure, cancellation); every member as judged.
/// </summary>
internal sealed record SemanticBatchRun(
    SemanticVerdict? ChildFailure,
    int? ExitCode,
    TimeSpan Elapsed,
    string Stdout,
    string Stderr,
    string Detail,
    ImmutableArray<SemanticBatchMember> Members);

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
        var (host, arguments) = SelfLaunch();
        arguments.AddRange(["semantic-worker", descriptorPath, resultPath]);
        if (mode == SemanticReplay.Mode.ExactSource) arguments.Add("--exact-source");
        return new SemanticWorkerCommand(host, arguments, new Dictionary<string, string>(), descriptorPath, resultPath);
    }

    /// <summary>This executable, and the entry assembly as the first argument when it runs under a host.</summary>
    private static (string Host, List<string> Arguments) SelfLaunch()
    {
        var host = System.Environment.ProcessPath ?? throw new InvalidOperationException("no process path");
        var entry = Assembly.GetEntryAssembly();
        var selfContained = entry is not null
            && string.Equals(Path.GetFileNameWithoutExtension(host), entry.GetName().Name, StringComparison.OrdinalIgnoreCase);
        var arguments = new List<string>();
        if (!selfContained && entry?.Location is { Length: > 0 } dll) arguments.Add(dll);
        return (host, arguments);
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
        var (verdict, summary, detail) = JudgeResult(descriptor.Case, command.ResultPath, exitCode);
        return Finish(new SemanticSupervisedRun(verdict, exitCode, clock.Elapsed, stdout.Text, stderr.Text,
            command.DescriptorPath, summary, detail));
    }

    /// <summary>
    /// The classification of one worker result document against the recorded case, shared by a
    /// single supervised run and every member of a batch (<see cref="RunBatch"/>): no result (a
    /// missing observation after a clean exit, otherwise a crash), an unreadable or malformed one, a
    /// nonzero exit, a result for another case, a required profile observation or path the worker
    /// did not admit — else the worker's own verdict.
    /// </summary>
    internal static (SemanticVerdict Verdict, SemanticDescriptor.ResultSummary? Summary, string Detail) JudgeResult(
        SemanticCase recorded, string resultPath, int exitCode)
    {
        if (!File.Exists(resultPath))
        {
            return (exitCode == 0 ? SemanticVerdict.MissingObservation : SemanticVerdict.Crash, null,
                $"worker exited with {exitCode.ToString(CultureInfo.InvariantCulture)} and wrote no result");
        }

        string text;
        try
        {
            text = SemanticReplay.ReadBounded(resultPath);
        }
        catch (Exception exception) when (exception is IOException or InvalidDataException)
        {
            return (SemanticVerdict.MalformedOutput, null, exception.Message);
        }

        if (!SemanticDescriptor.TryParseResult(text, out var summary, out var problem))
            return (SemanticVerdict.MalformedOutput, null, problem);

        if (exitCode != 0)
            return (SemanticVerdict.Crash, summary, $"worker wrote a result but exited with {exitCode.ToString(CultureInfo.InvariantCulture)}");

        if (summary.CaseId != recorded.CaseId)
            return (SemanticVerdict.MalformedOutput, summary, "worker result belongs to a different case");

        // Every profile the recorded case requires must appear in the worker's observations.
        if (summary.Verdict != SemanticVerdict.RecipeDrift)
        {
            var required = recorded.Profiles.Select(p => p + "/" + SemanticMember.BaseRole)
                .Concat(recorded.Members.Skip(1).Select(m => SemanticProfiles.SyncOptimized + "/" + m.Role));
            var missing = required.Where(p => !summary.ObservedProfiles.Contains(p, StringComparer.Ordinal))
                .ToList();
            if (missing.Count > 0)
                return (SemanticVerdict.MissingObservation, summary, "no observation for " + string.Join(", ", missing));
        }

        if (summary.Verdict == SemanticVerdict.Passed
            && (recorded.Paths & ~summary.CoverageResult.PathsExercised) != SemanticPath.None)
            return (SemanticVerdict.MissingObservation, summary, "worker did not admit every required path");

        return (summary.Verdict, summary, summary.Findings.IsEmpty ? summary.CaseId : summary.Findings[0]);
    }

    // ── Batches (exhaustive campaigns) ──────────────────────────────────────

    /// <summary>
    /// The fuzz consumer relaunching itself as <c>semantic-batch-worker MANIFEST</c>: one child that
    /// replays every descriptor its manifest lists, in order, in RECIPE mode.
    /// </summary>
    internal static SemanticBatchWorkerCommand SelfBatchWorker(string manifestPath)
    {
        var (host, arguments) = SelfLaunch();
        arguments.AddRange(["semantic-batch-worker", manifestPath]);
        return new SemanticBatchWorkerCommand(host, arguments, new Dictionary<string, string>(), manifestPath);
    }

    /// <summary>
    /// The manifest's directive line that replays every member in exact-source mode (a reduced or
    /// candidate member is not a recipe case); without it a batch runs in recipe mode.
    /// </summary>
    internal const string ExactSourceDirective = "#mode exact-source";

    /// <summary>
    /// The manifest of a batch: one <c>descriptor TAB result</c> line per member, in order, after the
    /// <see cref="ExactSourceDirective"/> when <paramref name="mode"/> is exact-source. A relative path
    /// is relative to the manifest's own directory, so a persisted reproducer replays from anywhere.
    /// The caller has persisted every descriptor before it writes the manifest.
    /// </summary>
    internal static void WriteManifest(
        string manifestPath, IEnumerable<(string Descriptor, string Result)> members, SemanticReplay.Mode mode = SemanticReplay.Mode.Recipe)
        => File.WriteAllText(manifestPath, (mode == SemanticReplay.Mode.ExactSource ? ExactSourceDirective + "\n" : "")
            + string.Concat(members.Select(static m => m.Descriptor + "\t" + m.Result + "\n")));

    /// <summary>
    /// Runs one batch child under the same bounds as a single worker: bounded output, the whole
    /// tree killed and awaited on expiry. The deadline is a PROGRESS deadline: it restarts whenever
    /// another member's result appears, so it bounds each member's execution as <see cref="Run"/>
    /// bounds one case. When the command names a readiness file
    /// (<see cref="SemanticBatchWorkerCommand.ReadyPath"/>), the progress deadline starts at readiness
    /// and <see cref="SemanticBatchWorkerCommand.StartupDeadline"/> bounds the time before it, exactly
    /// as <see cref="Run"/> does. Every member with a result is judged by <see cref="JudgeResult"/>; a member
    /// without one (in flight when the child crashed or timed out, or never reached) is returned
    /// unjudged, for the caller to rerun on its own. The child's supervision record is written next
    /// to the manifest.
    /// </summary>
    internal static SemanticBatchRun RunBatch(
        SemanticBatchWorkerCommand command, IReadOnlyList<SemanticBatchMember> members, TimeSpan deadline, CancellationToken cancellationToken = default)
    {
        ArgumentNullException.ThrowIfNull(command);
        ArgumentNullException.ThrowIfNull(members);
        foreach (var member in members) File.Delete(member.ResultPath); // a stale result must never masquerade as the worker's output
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
        SemanticVerdict? childFailure = null;
        var notReady = false;
        int? exitCode = null;
        string detail;
        try
        {
            process.Start();
            process.StandardInput.Close();
            var output = Task.WhenAll(ReadOutput(process.StandardOutput, stdout), ReadOutput(process.StandardError, stderr));
            if (command.ReadyPath is { } ready)
            {
                // The startup bound, as for a single worker: wait for readiness, the child's exit, or the
                // bound, whichever comes first. The progress deadline below starts only at readiness.
                var startup = Stopwatch.StartNew();
                while (childFailure is null && !File.Exists(ready) && !process.WaitForExit(TimeSpan.FromMilliseconds(50)))
                {
                    if (cancellationToken.IsCancellationRequested) childFailure = SemanticVerdict.SupervisorCancellation;
                    else if (startup.Elapsed > command.StartupDeadline) (childFailure, notReady) = (SemanticVerdict.Timeout, true);
                }

                if (childFailure is not null) Terminate(process);
            }

            var progress = Stopwatch.StartNew();
            var completed = 0;
            while (childFailure is null && !process.WaitForExit(TimeSpan.FromMilliseconds(100)))
            {
                var now = members.Count(static m => File.Exists(m.ResultPath));
                if (now != completed)
                {
                    completed = now;
                    progress.Restart();
                }

                if (cancellationToken.IsCancellationRequested || progress.Elapsed > deadline)
                {
                    childFailure = cancellationToken.IsCancellationRequested ? SemanticVerdict.SupervisorCancellation : SemanticVerdict.Timeout;
                    Terminate(process);
                    break;
                }
            }

            if (childFailure is null)
            {
                // Bounded like the single worker: the readers must finish within the deadline too.
                if (!output.Wait(deadline)) childFailure = SemanticVerdict.Timeout;
                exitCode = process.ExitCode;
                if (exitCode != 0) childFailure = SemanticVerdict.Crash;
            }
            else
            {
                output.Wait(TimeSpan.FromSeconds(5));
            }

            detail = childFailure switch
            {
                null => "batch worker exited with 0",
                SemanticVerdict.Timeout when notReady =>
                    $"batch worker not ready within {command.StartupDeadline.TotalSeconds.ToString(CultureInfo.InvariantCulture)}s; worker tree terminated",
                SemanticVerdict.Timeout => $"no member completed within {deadline.TotalSeconds.ToString(CultureInfo.InvariantCulture)}s; worker tree terminated",
                SemanticVerdict.SupervisorCancellation => "supervisor cancelled; worker tree terminated",
                _ => $"batch worker exited with {exitCode?.ToString(CultureInfo.InvariantCulture)}",
            };
        }
        catch (Exception exception) when (exception is System.ComponentModel.Win32Exception or InvalidOperationException)
        {
            childFailure = SemanticVerdict.HarnessFailure;
            detail = "batch worker could not be started: " + exception.Message;
        }

        // A member's result was written whole before the next member started: judge each on its own.
        var judged = members.Select(member =>
        {
            if (!File.Exists(member.ResultPath)) return member;
            var (verdict, summary, memberDetail) = JudgeResult(member.Case, member.ResultPath, 0);
            return member with { Verdict = verdict, Summary = summary, Detail = memberDetail };
        }).ToImmutableArray();
        var run = new SemanticBatchRun(childFailure, exitCode, clock.Elapsed, stdout.Text, stderr.Text, detail, judged);
        File.WriteAllText(command.ManifestPath + ".supervision.txt", JsonSerializer.Serialize(new
        {
            run.ChildFailure, run.ExitCode, run.Elapsed, command.ManifestPath, run.Detail, run.Stdout, run.Stderr,
            Members = judged.Select(static m => new { m.Case.CaseId, m.Verdict, m.Detail }),
        },
            new JsonSerializerOptions { WriteIndented = true }));
        return run;
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
