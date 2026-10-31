using System.Diagnostics;
using System.Globalization;
using System.Runtime.ExceptionServices;
using System.Text;

namespace KatLang.TestInfrastructure;

/// <summary>
/// Runs a parser termination sweep — an explicitly named <see cref="SubprocessProbe"/> that reports
/// through <see cref="TerminationProgress"/> — in a fresh process, and fails it when NO WORK ITEM
/// COMPLETES for a stall window.
/// <para>A parse that never returns cannot be interrupted in place (the parser observes no
/// cancellation in its recovery loops), so the sweep runs in a child that can be terminated. The
/// window bounds the time without completed work, never the total duration: a worker that keeps
/// completing items may run far longer than the window, and a window that expires is an observation
/// that no completion was SEEN, not a proof of a parser defect — operating-system scheduling can
/// still delay the child or the dedicated threads that observe it. These tests therefore establish
/// termination, not an aggregate performance bound.</para>
/// <para>Only a strictly increasing completed-work ordinal resets the window. Heartbeats, phase
/// changes, a repeated ordinal and a newly started item do not. The window starts at launch, so it
/// also covers process start-up until the first completion. Success requires exit code 0, exactly one
/// start and pass line for the probe, exactly one completion record with the expected count, and a
/// well-formed protocol; a completion line alone never turns a failing child into a pass.</para>
/// <para>Every path after the child is created ends and joins it: the child is terminated if still
/// running, its exit is awaited, and both output threads are joined. Output is consumed continuously
/// and retained only in bounded form, so the child never blocks on a full pipe. The child also ends
/// itself when its owner process is gone (<see cref="TerminationProgress"/>).</para>
/// </summary>
internal static class TerminationProbe
{
    public const string OwnerVariable = "KATLANG_TERMINATION_PROBE_OWNER";
    public const string ProgressPrefix = "TERMINATION PROGRESS ";
    public const string HeartbeatPrefix = "TERMINATION HEARTBEAT ";
    public const string FailedPrefix = "TERMINATION FAILED ";
    public const string CompletePrefix = "TERMINATION COMPLETE ";

    /// <summary>The stall window of the parser termination sweeps.</summary>
    public static readonly TimeSpan ParserStallWindow = TimeSpan.FromMinutes(2);

    private static readonly TimeSpan PollInterval = TimeSpan.FromMilliseconds(250);
    private const int StandardErrorLimit = 32 * 1024;

    /// <summary>Runs the probe and fails the calling test unless it completed successfully.</summary>
    public static TerminationRun RunAndAssert(Type probeType, string method, long expectedCompleted, TimeSpan stallWindow,
        IReadOnlyDictionary<string, string>? environment = null)
    {
        var run = Run(probeType, method, expectedCompleted, stallWindow, environment);
        if (run.Failure is not null)
            Assert.Fail(run.Failure);
        return run;
    }

    /// <summary>
    /// Runs the probe to completion or stall and returns the verdict. Operational failures of this
    /// harness (start-up, threads, cleanup) are thrown; the child's own outcome is the verdict.
    /// </summary>
    public static TerminationRun Run(Type probeType, string method, long expectedCompleted, TimeSpan stallWindow,
        IReadOnlyDictionary<string, string>? environment = null)
    {
        var probe = probeType.FullName + "." + method;
        var start = SubprocessProbe.StartInfo(probeType, method);
        if (environment is not null)
            foreach (var (name, value) in environment)
                start.Environment[name] = value;
        using (var self = Process.GetCurrentProcess())
            start.Environment[OwnerVariable] = OwnerIdentity(Environment.ProcessId, self.StartTime);

        var launched = Stopwatch.GetTimestamp();
        var monitor = new TerminationMonitor(probe, launched, stallWindow);
        var standardError = new BoundedText(StandardErrorLimit);
        using var process = Process.Start(start) ?? throw new InvalidOperationException($"The probe child did not start: {probe}");

        // From here on the child exists: every path below ends and joins it.
        Thread? output = null, errors = null;
        var stalled = false;
        ExceptionDispatchInfo? primary = null;
        try
        {
            monitor.RecordChild(process.Id);
            output = StartReader(process.StandardOutput, line => monitor.Observe(line, Stopwatch.GetTimestamp()), monitor, "termination-probe-stdout");
            errors = StartReader(process.StandardError, standardError.AppendLine, monitor, "termination-probe-stderr");
            // The window is checked on this thread with a blocking wait, never on the thread pool.
            while (!process.WaitForExit(PollInterval))
            {
                if (monitor.IsStalled(Stopwatch.GetTimestamp()))
                {
                    stalled = true;
                    break;
                }
            }
        }
        catch (Exception exception)
        {
            primary = ExceptionDispatchInfo.Capture(exception);
        }

        var cleanup = EndAndJoin(process, output, errors);
        if (primary is not null)
        {
            if (cleanup.Count == 0)
                primary.Throw();
            throw new AggregateException($"The termination probe {probe} failed, and so did its cleanup.", [primary.SourceException, .. cleanup]);
        }
        if (cleanup.Count > 0)
            throw new AggregateException($"The termination probe {probe} could not be ended and joined.", cleanup);

        var exitedAt = Stopwatch.GetTimestamp();
        return monitor.Evaluate(process.ExitCode, stalled, expectedCompleted, standardError.ToString(), exitedAt);
    }

    public static string OwnerIdentity(int processId, DateTime startTime)
        => string.Create(CultureInfo.InvariantCulture, $"{processId}:{startTime.ToUniversalTime().Ticks}");

    /// <summary>Escapes an input so that a protocol record stays on one line.</summary>
    public static string Escape(string text)
        => text.Replace("\\", "\\\\", StringComparison.Ordinal)
            .Replace("\r", "\\r", StringComparison.Ordinal)
            .Replace("\n", "\\n", StringComparison.Ordinal);

    private static Thread StartReader(StreamReader reader, Action<string> onLine, TerminationMonitor monitor, string name)
    {
        var thread = new Thread(() =>
        {
            try
            {
                for (string? line; (line = reader.ReadLine()) is not null;)
                    onLine(line);
            }
            catch (Exception exception)
            {
                monitor.ReaderFailed(name, exception);
            }
        })
        { IsBackground = true, Name = name };
        thread.Start();
        return thread;
    }

    private static List<Exception> EndAndJoin(Process process, Thread? output, Thread? errors)
    {
        var failures = new List<Exception>();
        try
        {
            if (!process.HasExited)
                process.Kill(entireProcessTree: true);
        }
        catch (InvalidOperationException) when (HasExited(process))
        {
            // It exited between the check and the kill.
        }
        catch (Exception exception)
        {
            // Waiting for a child that could not be terminated could block forever; report it instead.
            failures.Add(new InvalidOperationException(
                $"The probe child {SafeId(process)} could not be terminated and may still be running.", exception));
            return failures;
        }

        try
        {
            process.WaitForExit();
        }
        catch (Exception exception)
        {
            failures.Add(exception);
            return failures;
        }

        // The child is gone, so both pipes reach end of input and the readers finish.
        foreach (var thread in new[] { output, errors })
        {
            if (thread is not null && thread.ThreadState != System.Threading.ThreadState.Unstarted)
                thread.Join();
        }

        return failures;
    }

    private static bool HasExited(Process process)
    {
        try { return process.HasExited; }
        catch (InvalidOperationException) { return false; }
    }

    private static string SafeId(Process process)
    {
        try { return process.Id.ToString(CultureInfo.InvariantCulture); }
        catch (InvalidOperationException) { return "(unknown id)"; }
    }

    private sealed class BoundedText(int limit)
    {
        private readonly StringBuilder _text = new();
        private bool _truncated;

        public void AppendLine(string line)
        {
            lock (_text)
            {
                if (_text.Length + line.Length + 1 <= limit)
                    _text.Append(line).Append('\n');
                else
                    _truncated = true;
            }
        }

        public override string ToString()
        {
            lock (_text)
                return _truncated ? _text + $"[standard error truncated after {limit} characters]\n" : _text.ToString();
        }
    }
}

/// <summary>The verdict of one termination probe run: <see cref="Failure"/> is null exactly when it passed.</summary>
internal sealed record TerminationRun(string? Failure, string? Completion, int? ProcessId, TimeSpan? ProbeStarted, TimeSpan Exited);

/// <summary>
/// The parent's view of a termination probe's output: a thread-safe state machine fed one line at a
/// time. Completion timestamps use the machine-wide monotonic Stopwatch clock, so delayed pipe
/// records cannot renew the window with old work. Kept separate from the process so that the
/// window and protocol rules are testable with synthetic lines and times.
/// </summary>
internal sealed class TerminationMonitor(string probe, long launched, TimeSpan stallWindow)
{
    private const int TailLimit = 40;
    private const int RecordLimit = 8;

    private readonly object _gate = new();
    private readonly Queue<string> _tail = new();
    private readonly List<string> _failures = [];
    private readonly List<string> _protocolErrors = [];
    private readonly long _launched = launched;
    private long _lastAdvance = launched;
    private long _completed;
    private long _probeStarted;
    private int _starts;
    private int _passes;
    private int _completions;
    private string? _completion;
    private string? _lastProgress;
    private string? _lastHeartbeat;
    private int _childId;

    public long Completed { get { lock (_gate) return _completed; } }

    public void Observe(string line, long timestamp)
    {
        lock (_gate)
        {
            if (line.StartsWith(TerminationProbe.ProgressPrefix, StringComparison.Ordinal))
                ObserveProgress(line, timestamp);
            else if (line.StartsWith(TerminationProbe.HeartbeatPrefix, StringComparison.Ordinal))
                ObserveHeartbeat(line);
            else if (line.StartsWith(TerminationProbe.CompletePrefix, StringComparison.Ordinal))
            {
                _completions++;
                _completion ??= line;
            }
            else if (line.StartsWith(TerminationProbe.FailedPrefix, StringComparison.Ordinal))
                AddBounded(_failures, line);
            else if (line == "PROBE START " + probe)
            {
                _starts++;
                if (_probeStarted == 0)
                    _probeStarted = timestamp;
            }
            else if (line == "PROBE PASS " + probe)
                _passes++;
            else
            {
                if (_tail.Count == TailLimit)
                    _tail.Dequeue();
                _tail.Enqueue(line);
            }
        }
    }

    public void ReaderFailed(string reader, Exception exception)
    {
        lock (_gate)
            AddBounded(_protocolErrors, $"the {reader} reader failed: {exception.GetType().Name}: {exception.Message}");
    }

    /// <summary>True once no completed-work ordinal increase has been seen for the whole window.</summary>
    public bool IsStalled(long now)
    {
        lock (_gate)
            return Stopwatch.GetElapsedTime(_lastAdvance, now) > stallWindow;
    }

    public TerminationRun Evaluate(int exitCode, bool stalled, long expectedCompleted, string standardError, long exitedAt)
    {
        lock (_gate)
        {
            var failure = Failure(exitCode, stalled, expectedCompleted);
            var probeStarted = _probeStarted == 0 ? (TimeSpan?)null : Stopwatch.GetElapsedTime(_launched, _probeStarted);
            return new TerminationRun(
                failure is null ? null : failure + "\n" + Evidence(exitCode, standardError),
                _completion,
                _childId == 0 ? null : _childId,
                probeStarted,
                Stopwatch.GetElapsedTime(_launched, exitedAt));
        }
    }

    internal void RecordChild(int processId)
    {
        lock (_gate)
            _childId = processId;
    }

    private string? Failure(int exitCode, bool stalled, long expectedCompleted)
    {
        if (stalled)
            return $"No work item of {probe} completed for {stallWindow.TotalSeconds:0.###} s (completed so far: {_completed}), "
                + "so the child was terminated. The last progress record is an observation at that point, not a proven "
                + $"counterexample or a proven implementation defect: {_lastProgress ?? "none received"}";
        if (exitCode != 0)
            return $"The probe child of {probe} failed with exit code {exitCode}."
                + (_failures.Count > 0 ? " " + string.Join(" ", _failures) : "");
        if (_protocolErrors.Count > 0)
            return $"The probe child of {probe} exited 0 but its output broke the protocol: {string.Join("; ", _protocolErrors)}";
        if (_starts != 1 || _passes != 1)
            return $"Expected exactly one PROBE START and one PROBE PASS for {probe}; saw {_starts} and {_passes}.";
        if (_failures.Count > 0)
            return $"The probe child of {probe} exited 0 but reported a failure: {string.Join(" ", _failures)}";
        if (_completions != 1)
            return $"Expected exactly one completion record from {probe}; saw {_completions}.";
        var expected = $"{TerminationProbe.CompletePrefix}completed={expectedCompleted.ToString(CultureInfo.InvariantCulture)}";
        if (_completion != expected && !_completion!.StartsWith(expected + " ", StringComparison.Ordinal))
            return $"The completion record of {probe} does not report {expectedCompleted} completed items: {_completion}";
        if (_completed > expectedCompleted)
            return $"The progress of {probe} reported {_completed} completed items, more than the {expectedCompleted} expected.";
        return null;
    }

    private string Evidence(int exitCode, string standardError)
    {
        var text = new StringBuilder();
        text.Append(CultureInfo.InvariantCulture, $"exit code: {exitCode}; completed-work ordinal: {_completed}\n");
        text.Append($"last progress: {_lastProgress ?? "none"}\nlast heartbeat: {_lastHeartbeat ?? "none"}\n");
        foreach (var error in _protocolErrors)
            text.Append("protocol: ").Append(error).Append('\n');
        text.Append(CultureInfo.InvariantCulture, $"last {_tail.Count} other output lines:\n");
        foreach (var line in _tail)
            text.Append(line).Append('\n');
        text.Append("standard error:\n").Append(standardError);
        return text.ToString();
    }

    private void ObserveProgress(string line, long timestamp)
    {
        _lastProgress = line;
        // completed=<n> completedAt=<Stopwatch timestamp> started=<k> phase=<label> input=<escaped input>
        var fields = line.AsSpan(TerminationProbe.ProgressPrefix.Length);
        if (!TryField(ref fields, "completed=", out var completed)
            || !TryField(ref fields, "completedAt=", out var completedAt)
            || !TryField(ref fields, "started=", out var started)
            || !TryLabel(ref fields, "phase=")
            || !fields.StartsWith("input=", StringComparison.Ordinal))
        {
            AddBounded(_protocolErrors, $"malformed progress record: {line}");
            return;
        }
        if (completed < _completed)
        {
            AddBounded(_protocolErrors, $"the completed-work ordinal went back from {_completed}: {line}");
            return;
        }
        if (started != completed && started != completed + 1)
        {
            AddBounded(_protocolErrors, $"the started item is neither the completed nor the next one: {line}");
            return;
        }
        if ((completed == 0 && completedAt != 0)
            || (completed > 0 && (completedAt < _launched || completedAt > timestamp))
            || (completed > _completed && completedAt < _lastAdvance))
        {
            AddBounded(_protocolErrors, $"invalid completion timestamp: {line}");
            return;
        }
        if (completed == _completed && completed > 0 && completedAt != _lastAdvance)
        {
            AddBounded(_protocolErrors, $"a repeated ordinal changed its completion timestamp: {line}");
            return;
        }
        if (completed > _completed)
        {
            _completed = completed;
            _lastAdvance = completedAt;
        }
    }

    private void ObserveHeartbeat(string line)
    {
        _lastHeartbeat = line;
        var fields = line.AsSpan(TerminationProbe.HeartbeatPrefix.Length);
        if (!TryField(ref fields, "completed=", out var completed) || !fields.IsEmpty)
            AddBounded(_protocolErrors, $"malformed heartbeat: {line}");
        else if (completed != _completed)
            AddBounded(_protocolErrors, $"a heartbeat reported {completed} completed items, but progress reported {_completed}: {line}");
    }

    private static bool TryField(ref ReadOnlySpan<char> fields, string name, out long value)
    {
        value = 0;
        if (!fields.StartsWith(name, StringComparison.Ordinal))
            return false;
        var rest = fields[name.Length..];
        var end = rest.IndexOf(' ');
        var digits = end < 0 ? rest : rest[..end];
        if (digits.IsEmpty || !long.TryParse(digits, NumberStyles.None, CultureInfo.InvariantCulture, out value))
            return false;
        fields = end < 0 ? [] : rest[(end + 1)..];
        return true;
    }

    private static bool TryLabel(ref ReadOnlySpan<char> fields, string name)
    {
        if (!fields.StartsWith(name, StringComparison.Ordinal))
            return false;
        var rest = fields[name.Length..];
        var end = rest.IndexOf(' ');
        if (end <= 0)
            return false;
        fields = rest[(end + 1)..];
        return true;
    }

    private static void AddBounded(List<string> records, string record)
    {
        if (records.Count < RecordLimit)
            records.Add(record);
    }
}

/// <summary>
/// The child side of <see cref="TerminationProbe"/>: the sweep announces each work item with
/// <see cref="Begin"/>, its later phases with <see cref="Enter"/>, and its completion — after the
/// item's parses AND assertions — with <see cref="Complete"/>. A dedicated reporter thread samples
/// one coherent snapshot every quarter second and prints a progress record when it changed, or a
/// heartbeat about once a second when it did not, so output stays bounded by time, not by item
/// count. The same thread ends the process (exit code <see cref="OwnerGoneExitCode"/>) once the
/// owning test process is gone, so a hung child does not outlive its owner.
/// </summary>
internal sealed class TerminationProgress : IDisposable
{
    public const int OwnerGoneExitCode = 3;

    private static readonly TimeSpan ReportInterval = TimeSpan.FromMilliseconds(250);
    private const int QuietReportsPerHeartbeat = 4;

    private sealed record State(long Started, long Completed, long CompletedAt, string Phase, string Input);

    private readonly ManualResetEventSlim _stop = new();
    private readonly Process? _owner;
    private readonly Thread _reporter;
    private State _state = new(0, 0, 0, "starting", "");
    private bool _stopped;
    private bool _finished;

    private TerminationProgress(Process? owner)
    {
        _owner = owner;
        _reporter = new Thread(Report) { IsBackground = true, Name = "termination-progress" };
        _reporter.Start();
    }

    /// <summary>Starts reporting; ends the process at once when the owner named by the parent is already gone.</summary>
    public static TerminationProgress Start()
        => new(Environment.GetEnvironmentVariable(TerminationProbe.OwnerVariable) is { } owner ? OpenOwner(owner) : null);

    public long Completed => Volatile.Read(ref _state).Completed;

    public void Begin(long ordinal, string phase, string input)
    {
        var state = Volatile.Read(ref _state);
        if (ordinal != state.Completed + 1 || state.Started != state.Completed)
            throw new InvalidOperationException($"Item #{ordinal} cannot start after #{state.Started} with {state.Completed} completed.");
        Volatile.Write(ref _state, new State(ordinal, state.Completed, state.CompletedAt, Label(phase), input));
    }

    public void Enter(string phase)
    {
        var state = Volatile.Read(ref _state);
        if (state.Started == state.Completed)
            throw new InvalidOperationException("No item is in progress.");
        Volatile.Write(ref _state, state with { Phase = Label(phase) });
    }

    public void Complete()
    {
        var state = Volatile.Read(ref _state);
        if (state.Started != state.Completed + 1)
            throw new InvalidOperationException("No item is in progress.");
        Volatile.Write(ref _state, state with { Completed = state.Started, CompletedAt = Stopwatch.GetTimestamp() });
    }

    /// <summary>For an exception filter: prints the failing item and phase, and never catches.</summary>
    public bool ReportFailure()
    {
        var state = Volatile.Read(ref _state);
        Console.WriteLine($"{TerminationProbe.FailedPrefix}input #{state.Started} during the {state.Phase} phase: {TerminationProbe.Escape(state.Input)}");
        return false;
    }

    /// <summary>Stops the reporter and prints the one completion record, after a final progress record.</summary>
    public void Finish(string summary)
    {
        if (_finished)
            throw new InvalidOperationException("The sweep was already finished.");
        _finished = true;
        StopReporter();
        var state = Volatile.Read(ref _state);
        if (state.Started != state.Completed)
            throw new InvalidOperationException($"Item #{state.Started} is still in progress.");
        Print(state);
        Console.WriteLine($"{TerminationProbe.CompletePrefix}completed={state.Completed.ToString(CultureInfo.InvariantCulture)} {summary}");
    }

    public void Dispose()
    {
        StopReporter();
        _owner?.Dispose();
        _stop.Dispose();
    }

    private void StopReporter()
    {
        if (_stopped)
            return;
        _stopped = true;
        _stop.Set();
        _reporter.Join();
    }

    private void Report()
    {
        State? reported = null;
        var quiet = 0;
        while (!_stop.Wait(ReportInterval))
        {
            if (_owner is { HasExited: true })
                Environment.Exit(OwnerGoneExitCode); // Nothing is left to end and join this child.
            var state = Volatile.Read(ref _state);
            if (!ReferenceEquals(state, reported))
            {
                Print(state);
                reported = state;
                quiet = 0;
            }
            else if (++quiet == QuietReportsPerHeartbeat)
            {
                Console.WriteLine($"{TerminationProbe.HeartbeatPrefix}completed={state.Completed.ToString(CultureInfo.InvariantCulture)}");
                quiet = 0;
            }
        }
    }

    private static void Print(State state)
        => Console.WriteLine(
            $"{TerminationProbe.ProgressPrefix}completed={state.Completed.ToString(CultureInfo.InvariantCulture)} "
            + $"completedAt={state.CompletedAt.ToString(CultureInfo.InvariantCulture)} "
            + $"started={state.Started.ToString(CultureInfo.InvariantCulture)} phase={state.Phase} input={TerminationProbe.Escape(state.Input)}");

    private static string Label(string phase)
        => phase.Length > 0 && !phase.Any(char.IsWhiteSpace)
            ? phase
            : throw new ArgumentException("A phase label is one nonempty word.", nameof(phase));

    private static Process OpenOwner(string identity)
    {
        var separator = identity.IndexOf(':');
        if (separator < 1)
            throw new FormatException($"Invalid {TerminationProbe.OwnerVariable}: {identity}");
        var id = int.Parse(identity.AsSpan(0, separator), CultureInfo.InvariantCulture);
        Process owner;
        try
        {
            owner = Process.GetProcessById(id);
        }
        catch (ArgumentException)
        {
            Environment.Exit(OwnerGoneExitCode);
            throw; // Unreachable.
        }
        // A reused process id names a different process: the owner is gone.
        if (TerminationProbe.OwnerIdentity(id, owner.StartTime) != identity || owner.HasExited)
        {
            owner.Dispose();
            Environment.Exit(OwnerGoneExitCode);
        }
        return owner;
    }
}
