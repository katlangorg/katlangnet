using System.Diagnostics;
using System.Globalization;
using System.Reflection;
using System.Runtime.ExceptionServices;
using Xunit.Abstractions;

namespace KatLang.TestInfrastructure;

/// <summary>
/// The secondary completion safeguard for FrontEndDagComplexityTests. Each row invokes its ACTUAL
/// test method in an owned child, using the test assembly's dependencies and runtime settings.
/// Both the initial worker and async continuations use pool threads with an explicit 1 MiB stack.
/// Exact expansion counts and sharing assertions remain the primary complexity oracle.
/// </summary>
internal static class DagTraversalProbe
{
    private const string TypeVariable = "KATLANG_DAG_PROBE_TYPE";
    private const string MethodVariable = "KATLANG_DAG_PROBE_METHOD";
    private const string DepthVariable = "KATLANG_DAG_PROBE_DEPTH";
    private const string CountVariable = "KATLANG_DAG_PROBE_COUNT";
    internal static readonly TimeSpan StallWindow = TimeSpan.FromSeconds(30);
    private static readonly AsyncLocal<Work?> Current = new();

    internal static Task Guard(Type type, string method, int? depth, long expectedCompleted,
        Func<Task> body, ITestOutputHelper? output = null, TimeSpan? stallWindow = null)
    {
        if (Current.Value is { } work)
        {
            Assert.Equal((work.Type, work.Method, work.Depth, work.ExpectedCompleted),
                (type, method, depth, expectedCompleted));
            return work.Execute(body);
        }

        var identity = Identity(type, method, depth);
        var run = Run(type, method, depth, expectedCompleted, stallWindow);
        if (run.Failure is not null)
            Assert.Fail(run.Failure);
        Assert.Contains("case=" + identity + " ", run.Completion!, StringComparison.Ordinal);
        var summary = $"{run.Completion}; launch-to-exit={run.Exited.TotalSeconds:0.000}s";
        if (output is null) Console.WriteLine(summary);
        else output.WriteLine(summary);
        return Task.CompletedTask;
    }

    internal static TerminationRun Run(Type type, string method, int? depth, long expectedCompleted,
        TimeSpan? stallWindow = null)
        => TerminationProbe.Run(typeof(DagTraversalProbe), nameof(Execute),
            expectedCompleted, stallWindow ?? StallWindow, new Dictionary<string, string>
            {
                [TypeVariable] = type.FullName!,
                [MethodVariable] = method,
                [DepthVariable] = depth?.ToString(CultureInfo.InvariantCulture) ?? "none",
                [CountVariable] = expectedCompleted.ToString(CultureInfo.InvariantCulture),
                // CLR configuration values are hexadecimal: 0x100000 = 1 MiB. Pin both prefixes
                // so an inherited stack override cannot silently change the calibrated witnesses.
                ["DOTNET_DefaultStackSize"] = "100000",
                ["COMPlus_DefaultStackSize"] = "100000",
            });

    /// <summary>
    /// Called only AFTER an operation and its assertions have returned. No heartbeat, phase entry,
    /// queued output or repeated snapshot renews the guard. Most cases have one atomic body; the
    /// selected loader path additionally completes eager passes and each verified materialized level.
    /// </summary>
    internal static void Completed(string operation)
    {
        var progress = Current.Value?.Progress ?? throw new InvalidOperationException("No DAG probe is running.");
        progress.Enter(operation);
        progress.Complete();
        progress.Begin(progress.Completed + 1, "following-completion", operation);
    }

    // Explicit SubprocessProbe entry point, never an xUnit-discovered test.
    public static async Task Execute()
    {
        var type = typeof(DagTraversalProbe).Assembly.GetType(Required(TypeVariable), throwOnError: true)!;
        var methodName = Required(MethodVariable);
        var depthText = Required(DepthVariable);
        int? depth = depthText == "none" ? null : int.Parse(depthText, CultureInfo.InvariantCulture);
        var expected = long.Parse(Required(CountVariable), CultureInfo.InvariantCulture);
        var method = type.GetMethod(methodName, BindingFlags.Public | BindingFlags.Instance | BindingFlags.DeclaredOnly)
            ?? throw new MissingMethodException(type.FullName, methodName);
        Assert.Equal(typeof(Task), method.ReturnType);
        Assert.Equal(depth.HasValue ? new[] { typeof(int) } : [], method.GetParameters().Select(p => p.ParameterType));
        // Forward the exact requested argument, also for direct reuse of a theory's work by a
        // neighboring test (the exposure-sharing controls call the selected-path body at 3/6).
        // Guard checks this identity/depth again before executing the lambda. xUnit owns discovery.
        Assert.Equal("100000", Required("DOTNET_DefaultStackSize"));
        Assert.Equal("100000", Required("COMPlus_DefaultStackSize"));

        using var progress = TerminationProgress.Start();
        var work = new Work(type, methodName, depth, expected, progress);
        Current.Value = work;
        try
        {
            var instance = SubprocessProbe.CreateInstance(type);
            Task task;
            try { task = (Task)method.Invoke(instance, depth.HasValue ? [depth.Value] : null)!; }
            catch (TargetInvocationException exception) when (exception.InnerException is not null)
            {
                ExceptionDispatchInfo.Capture(exception.InnerException).Throw();
                throw;
            }
            await task;
            Assert.True(work.Executed, "The selected method did not execute its guarded body.");
        }
        finally { Current.Value = null; }
    }

    private static string Required(string variable)
        => Environment.GetEnvironmentVariable(variable) ?? throw new InvalidOperationException($"Missing {variable}.");

    private static string Identity(Type type, string method, int? depth)
        => $"{type.FullName}.{method}(depth={depth?.ToString(CultureInfo.InvariantCulture) ?? "none"})";

    private sealed class Work(Type type, string method, int? depth, long expectedCompleted, TerminationProgress progress)
    {
        internal Type Type { get; } = type;
        internal string Method { get; } = method;
        internal int? Depth { get; } = depth;
        internal long ExpectedCompleted { get; } = expectedCompleted;
        internal TerminationProgress Progress { get; } = progress;
        internal bool Executed { get; private set; }

        internal async Task Execute(Func<Task> body)
        {
            Assert.False(Executed, "A case must execute exactly one guarded body.");
            Executed = true;
            var identity = Identity(Type, Method, Depth);
            Progress.Begin(1, "worker-queued", identity);
            var queued = Stopwatch.GetTimestamp();
            await Task.Run(async () =>
            {
                var began = Stopwatch.GetTimestamp();
                using var self = Process.GetCurrentProcess();
                var cpu = self.TotalProcessorTime;
                var pauses = GC.GetTotalPauseDuration();
                try
                {
                    Assert.True(Thread.CurrentThread.IsThreadPoolThread);
                    Progress.Enter("body");
                    await body();
                    Progress.Complete();
                    Assert.Equal(ExpectedCompleted, Progress.Completed);
                    Progress.Finish(string.Create(CultureInfo.InvariantCulture,
                        $"case={identity} configuredStackBytes=1048576 pool=True queueMs={Stopwatch.GetElapsedTime(queued, began).TotalMilliseconds:0.###} activeWallMs={Stopwatch.GetElapsedTime(began).TotalMilliseconds:0.###} processCpuMs={(self.TotalProcessorTime - cpu).TotalMilliseconds:0.###} gcPauseMs={(GC.GetTotalPauseDuration() - pauses).TotalMilliseconds:0.###}"));
                }
                catch (Exception) when (Progress.ReportFailure())
                {
                    throw; // The filter reports context while preserving the original assertion/exception.
                }
            });
        }
    }
}
