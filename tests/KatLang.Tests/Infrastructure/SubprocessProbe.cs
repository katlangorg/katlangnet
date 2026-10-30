using System.Diagnostics;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.ExceptionServices;
using Xunit;
using Xunit.Abstractions;

namespace KatLang.TestInfrastructure;

/// <summary>
/// Fresh-process probe execution using the test assembly's dependencies and runtime settings.
/// Only named methods run: no VSTest startup, discovery, retries or elapsed-time deadline.
/// Shared as source with the CLI tests, like the GC-isolated allocation helper.
/// </summary>
internal static class SubprocessProbe
{
    public static ProcessStartInfo StartInfo(Type type, string method)
        => StartInfo(type.Assembly, [type.FullName + "." + method]);

    public static ProcessStartInfo StartInfo(Assembly assembly, IReadOnlyList<string> methods)
    {
        ArgumentNullException.ThrowIfNull(assembly);
        return StartInfo(assembly.Location, methods);
    }

    public static ProcessStartInfo StartInfo(string assemblyPath, IReadOnlyList<string> methods)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(assemblyPath);
        ArgumentNullException.ThrowIfNull(methods);
        if (methods.Count == 0)
            throw new ArgumentException("At least one probe must be named.", nameof(methods));

        var start = new ProcessStartInfo("dotnet")
        {
            UseShellExecute = false,
            CreateNoWindow = true,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
        };
        start.ArgumentList.Add("exec");
        start.ArgumentList.Add("--runtimeconfig");
        start.ArgumentList.Add(Path.ChangeExtension(assemblyPath, ".runtimeconfig.json"));
        start.ArgumentList.Add("--depsfile");
        start.ArgumentList.Add(Path.ChangeExtension(assemblyPath, ".deps.json"));
        start.ArgumentList.Add(typeof(global::KatLang.TestProbeHost.Program).Assembly.Location);
        start.ArgumentList.Add(assemblyPath);
        foreach (var method in methods)
            start.ArgumentList.Add(method);
        start.Environment["DOTNET_NOLOGO"] = "1";
        return start;
    }

    /// <summary>Called only by the probe executable, after the parent's environment is installed.</summary>
    public static async Task ExecuteAsync(string[] methods)
    {
        if (methods.Length == 0 || methods.Distinct(StringComparer.Ordinal).Count() != methods.Length)
            throw new ArgumentException("Probe names must be nonempty and unique.", nameof(methods));

        var assembly = typeof(SubprocessProbe).Assembly;
        foreach (var name in methods)
        {
            var separator = name.LastIndexOf('.');
            if (separator < 1)
                throw new ArgumentException($"Invalid probe name: {name}");
            var type = assembly.GetType(name[..separator], throwOnError: true)!;
            var method = type.GetMethod(name[(separator + 1)..], BindingFlags.Public | BindingFlags.Instance | BindingFlags.Static | BindingFlags.DeclaredOnly)
                ?? throw new MissingMethodException(type.FullName, name[(separator + 1)..]);
            if (method.GetParameters().Length != 0 || method.ContainsGenericParameters
                || (method.ReturnType != typeof(void) && method.ReturnType != typeof(Task) && method.ReturnType != typeof(ValueTask))
                || (method.ReturnType == typeof(void) && method.IsDefined(typeof(AsyncStateMachineAttribute))))
                throw new InvalidOperationException($"Probe must be a parameterless void, Task or ValueTask method: {name}");

            Console.WriteLine($"PROBE START {name}");
            var instance = method.IsStatic ? null : CreateInstance(type);
            try
            {
                if (instance is IAsyncLifetime lifetime)
                    await lifetime.InitializeAsync();
                object? result;
                try { result = method.Invoke(instance, null); }
                catch (TargetInvocationException exception) when (exception.InnerException is not null)
                {
                    ExceptionDispatchInfo.Capture(exception.InnerException).Throw();
                    throw;
                }
                if (result is Task task) await task;
                else if (result is ValueTask valueTask) await valueTask;
            }
            finally
            {
                if (instance is IAsyncLifetime lifetime) await lifetime.DisposeAsync();
                if (instance is IAsyncDisposable asyncDisposable) await asyncDisposable.DisposeAsync();
                else if (instance is IDisposable disposable) disposable.Dispose();
            }
            Console.WriteLine($"PROBE PASS {name}");
        }
    }

    private static object CreateInstance(Type type)
    {
        if (type.GetConstructor(Type.EmptyTypes) is { } plain)
            return plain.Invoke(null);
        if (type.GetConstructor([typeof(ITestOutputHelper)]) is { } withOutput)
            return withOutput.Invoke([new ConsoleOutput()]);
        throw new InvalidOperationException($"Probe class requires an unsupported fixture: {type.FullName}");
    }

    private sealed class ConsoleOutput : ITestOutputHelper
    {
        public void WriteLine(string message) => Console.WriteLine(message);
        public void WriteLine(string format, params object[] args) => Console.WriteLine(format, args);
    }
}
