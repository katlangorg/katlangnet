using System.Reflection;
using System.Runtime.Loader;

namespace KatLang.TestProbeHost;

/// <summary>Starts explicitly named probes without a test runner or assembly-wide discovery.</summary>
public static class Program
{
    public static async Task<int> Main(string[] arguments)
    {
        try
        {
            if (arguments.Length < 2)
                throw new ArgumentException("Expected a test assembly and at least one fully qualified probe method.");

            var assembly = AssemblyLoadContext.Default.LoadFromAssemblyPath(Path.GetFullPath(arguments[0]));
            var dispatcher = assembly.GetType("KatLang.TestInfrastructure.SubprocessProbe", throwOnError: true)!
                .GetMethod("ExecuteAsync", BindingFlags.Public | BindingFlags.Static)
                ?? throw new MissingMethodException("The test assembly has no subprocess probe dispatcher.");
            // Match test-runner worker-thread execution, including the runtime's configured stack size.
            await Task.Run(() => (Task)dispatcher.Invoke(null, [arguments[1..]])!);
            return 0;
        }
        catch (Exception exception)
        {
            Console.Error.WriteLine(exception is TargetInvocationException { InnerException: { } cause } ? cause : exception);
            return 1;
        }
    }
}
